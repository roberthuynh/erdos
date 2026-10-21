"""Pure mathematical input binding. This module never authenticates proof evidence."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tomllib

POLICY = 'accepted-mathematical-inputs-v1'
NAME = re.compile(r'[A-Za-z_][A-Za-z_0-9.]*')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def digest(value):
    return hashlib.sha256(value).hexdigest()


def read(root, relative):
    rel = PurePosixPath(relative)
    if not isinstance(relative, str) or not rel.parts or rel.is_absolute() or '..' in rel.parts or str(rel) != relative:
        raise ValueError('Unsafe mathematical input path')
    path = Path(root)
    for part in rel.parts:
        path = path / part
        if path.is_symlink():
            raise ValueError('Symlink mathematical input')
    if not path.is_file():
        raise ValueError('Missing mathematical input: ' + relative)
    return path.read_bytes()


def lean_code(data):
    """Remove comments only; preserve code spacing, indentation and literal bytes.

    Blank lines left by standalone comments are omitted. Inline comment columns
    are preserved, so uncertain inline edits fail equivalence conservatively.
    """
    text = data.decode('utf-8') if isinstance(data, bytes) else data
    result = []
    index = depth = 0
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == '/-': depth += 1; result.extend('  '); index += 2
            elif pair == '-/': depth -= 1; result.extend('  '); index += 2
            else: result.append('\n' if char == '\n' else ' '); index += 1
        elif pair == '/-': depth = 1; result.extend('  '); index += 2
        elif pair == '--':
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
        elif char in {'"', '«'}:
            start = index
            close = '"' if char == '"' else '»'
            index += 1
            while index < len(text):
                char = text[index]; index += 1
                if char == '\\' and close == '"':
                    if index >= len(text): raise ValueError('Unterminated Lean literal')
                    index += 1
                elif char == close: break
            else: raise ValueError('Unterminated Lean literal')
            result.append('"literal:' + digest(text[start:index].encode()) + '"')
        elif char == "'" and (match := re.match(r"'(?:\\.|[^\\'\n])'", text[index:])):
            result.append(match[0]); index += len(match[0])
        else: result.append(char); index += 1
    if depth: raise ValueError('Unterminated Lean comment')
    return '\n'.join(line.rstrip() for line in ''.join(result).splitlines() if line.strip()).encode()


def configured_modules(package):
    package = Path(package)
    config = tomllib.loads(read(package, 'lakefile.toml').decode())
    modules = {}
    for lib in config.get('lean_lib', []):
        for glob in lib.get('globs', [lib['name'], lib['name'] + '.+']):
            prefix = glob[:-2] if glob.endswith('.+') else glob
            if not NAME.fullmatch(prefix): raise ValueError('Unsupported Lean module glob')
            location = package / prefix.replace('.', '/')
            paths = location.rglob('*.lean') if glob.endswith('.+') and location.is_dir() else [location.with_suffix('.lean')] if not glob.endswith('.+') else []
            for path in paths:
                if not path.is_file(): continue
                rel = path.relative_to(package).as_posix()
                if '.lake' in path.relative_to(package).parts: continue
                read(package, rel)
                modules[rel[:-5].replace('/', '.')] = rel
    if not modules: raise ValueError('No configured Lean modules')
    return dict(sorted(modules.items()))


def project(package, configuration, *, accepted_axioms=None):
    """Bind a main package; accepted_axioms comes only from authenticated evidence.

    Source raw hashes are kept separately from the mathematical projection. A
    caller must validate phased projects separately, never silently omit them.
    """
    package = Path(package)
    modules = configured_modules(package)
    raw = {module: {'path': rel, 'sha256': digest(read(package, rel))} for module, rel in modules.items()}
    sources = {module: {'path': rel, 'lean_code_sha256': digest(lean_code(read(package, rel)))} for module, rel in modules.items()}
    entries = json.loads(read(package, configuration['registry']))
    declarations = []
    seen = set()
    for row in entries:
        name, module, typ = row['declaration'], row['module'], row['type']
        if not isinstance(name, str) or not name or '\n' in name or name in seen or module not in modules or not isinstance(typ, str) or not typ.strip():
            raise ValueError('Invalid declaration inventory')
        seen.add(name)
        axioms = row.get('axioms', (accepted_axioms or {}).get(name))
        if not isinstance(axioms, list) or len(axioms) != len(set(axioms)) or not set(axioms) <= ALLOWED_AXIOMS:
            raise ValueError('Missing or disallowed declaration axiom closure: ' + name)
        if accepted_axioms is not None and (name not in accepted_axioms or set(axioms) != set(accepted_axioms[name])):
            raise ValueError('Registered axioms differ from accepted evidence')
        declarations.append(dict(name=name, module=module, type_sha256=digest(typ.encode()), axioms=sorted(axioms), oracle=row.get('oracle') is True))
    if not declarations: raise ValueError('Empty declaration inventory')
    inputs = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}
    inputs.update(configuration[k] for k in ['coverage', 'axioms', 'replay', 'oracle'])
    for folder in ['scripts', 'tools']:
        if (package / folder).is_dir():
            inputs.update(p.relative_to(package).as_posix() for p in (package / folder).rglob('*')
                          if p.is_file() and p.suffix in {'.py', '.sh', '.lean'} and '__pycache__' not in p.parts)
    if (package / 'Axioms.lean').is_file(): inputs.add('Axioms.lean')
    projection = dict(schema=1, policy=POLICY, configuration=configuration, sources=sources,
                      declarations=sorted(declarations, key=lambda row: row['name']),
                      inputs={name: digest(read(package, name)) for name in sorted(inputs)},
                      coverage=dict(modules=list(modules), oracles=sorted(row['name'] for row in declarations if row['oracle'])))
    return dict(projection=projection, mathematical_input_sha256=digest(canonical(projection)), raw_sources=raw)


def phased_project(package, descriptor):
    """Recompute a phased binding from a complete, previously authenticated scope."""
    expected = {'path', 'configuration', 'plan_sha256', 'registry', 'sources', 'inputs', 'declarations', 'mathematical_input_sha256'}
    if set(descriptor) != expected: raise ValueError('Incomplete phased input descriptor')
    cfg = descriptor['configuration']
    if set(cfg) != {'path','plan','profile'} or cfg['path'] != descriptor['path']:
        raise ValueError('Invalid phased configuration')
    plan_sha = digest(read(package, cfg['plan']))
    read(package, descriptor['path'] + '/' + descriptor['registry'])
    root = Path(package) / descriptor['path']
    sources, inputs = descriptor['sources'], descriptor['inputs']
    if not sources or not inputs or set(sources) & set(inputs): raise ValueError('Invalid phased input membership')
    actual_lean = set()
    mandatory = {'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', descriptor['registry']}
    for p in root.rglob('*'):
        parts = p.relative_to(root).parts
        if not p.is_file() or set(parts) & {'.lake', '.verified-final', 'receipts', '__pycache__'}: continue
        name = p.relative_to(root).as_posix()
        if p.suffix == '.lean': actual_lean.add(name)
        if p.suffix in {'.py', '.sh', '.toml'} or parts[0] == 'pins': mandatory.add(name)
    if not mandatory <= set(inputs): raise ValueError('Missing phased checker or dependency input')
    if actual_lean != set(sources) | {n for n in inputs if n.endswith('.lean')}:
        raise ValueError('Missing or added phased Lean source')
    current_sources = {name: dict(sha256=digest(read(root, name)), lean_code_sha256=digest(lean_code(read(root, name)))) for name in sources}
    current_inputs = {name: digest(read(root, name)) for name in inputs}
    scope = json.loads(read(root, descriptor['registry']))['declarations']
    rows = descriptor['declarations']
    if (len(rows) != len(scope) or {r['name']: r['module'] for r in rows} != scope
            or descriptor['registry'] not in inputs): raise ValueError('Incomplete phased declaration scope')
    for row in rows:
        if set(row) != {'name','module','source_statement_sha256','axioms'}: raise ValueError('Invalid phased declaration')
        source = row['module'].replace('.', '/') + '.lean'
        if source not in current_sources or not set(row['axioms']) <= ALLOWED_AXIOMS:
            raise ValueError('Invalid phased declaration source or axioms')
        if row['source_statement_sha256'] != current_sources[source]['lean_code_sha256']:
            raise ValueError('Phased statement/proof input changed')
    projection = dict(path=descriptor['path'], configuration=cfg, plan_sha256=plan_sha, registry=descriptor['registry'],
                      sources={name: value['lean_code_sha256'] for name,value in current_sources.items()},
                      inputs=current_inputs, declarations=rows)
    return dict(path=descriptor['path'], configuration=cfg, plan_sha256=plan_sha, registry=descriptor['registry'], sources=current_sources,
                inputs=current_inputs, declarations=rows, mathematical_input_sha256=digest(canonical(projection)))
