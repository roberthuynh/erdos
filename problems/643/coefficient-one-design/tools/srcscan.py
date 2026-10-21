"""Secondary source scan for the phased verifier. Nested-comment-safe: strips `--` line comments, nested `/- ... -/`
block comments (doc comments included) and string/char literals with a small state machine, then counts whole tokens.
Usage: python3 -I srcscan.py FILE... ; prints one line per file and exits 1 if anything is flagged.
The primary check is environment-based (tools/Hygiene.lean) plus the kernel replay (leanchecker); this scan only
catches source-level constructs the environment cannot show (set_option, run_cmd, #eval, elab/macro, imports)."""
import re
import sys

FORBIDDEN = {'sorry', 'admit', 'native_decide', 'native', 'ofReduceBool', 'trustCompiler', 'axiom', 'opaque',
             'implemented_by', 'extern', 'unsafe', 'partial', 'run_cmd', 'run_elab', 'run_meta', '#eval', '#exit',
             'elab', 'elab_rules', 'macro', 'macro_rules', 'syntax', 'addDecl', 'skipKernelTC'}
ALLOWED_OPTIONS = {'autoImplicit'}
TOKEN = re.compile(r"#?[^\W\d][\w'!?.]*")


def strip(src):
    """Replace comments and string/char literals by blanks (newlines kept); block comments nest."""
    out = []
    i, n, depth = 0, len(src), 0

    def ident_char(ch):
        return ch.isalnum() or ch in "_'!?"

    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ''
        if depth > 0:
            if c == '/' and nxt == '-':
                depth += 1; out.append('  '); i += 2; continue
            if c == '-' and nxt == '/':
                depth -= 1; out.append('  '); i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if c == '/' and nxt == '-':
            depth = 1; out.append('  '); i += 2; continue
        if c == '-' and nxt == '-':
            while i < n and src[i] != '\n':
                out.append(' '); i += 1
            continue
        if c == '"':
            out.append(' '); i += 1
            while i < n and src[i] != '"':
                if src[i] == '\\':
                    out.append(' '); i += 1
                out.append('\n' if i < n and src[i] == '\n' else ' '); i += 1
            out.append(' '); i += 1; continue
        if c == "'" and (i == 0 or not ident_char(src[i - 1])):
            m = re.match(r"'(\\.[^']*|[^'\\])'", src[i:])
            if m:
                out.append(' ' * len(m.group(0))); i += len(m.group(0)); continue
        out.append(c); i += 1
    if depth != 0:
        raise SystemExit('unterminated block comment')
    return ''.join(out)


def scan(path):
    code = strip(open(path, encoding='utf-8').read())
    bad = {}
    for tok in TOKEN.findall(code):
        for part in tok.split('.'):
            if part in FORBIDDEN:
                bad[part] = bad.get(part, 0) + 1
                break
    if '+native' in re.sub(r'\s+', '', code):
        bad['+native'] = bad.get('+native', 0) + 1
    if re.search(r'(?<![A-Za-z0-9_])_unsafe_rec\b', code):
        bad['explicit_generated_helper_name'] = 1
    opts = sorted(set(re.findall(r"\bset_option\s+([^\W\d][\w.]*)", code)))
    badopts = [o for o in opts if o not in ALLOWED_OPTIONS]
    imports = re.findall(r"^\s*import\s+(\S+)", code, flags=re.M)
    badimports = [m for m in imports if not (m == 'Mathlib' or m.startswith('Mathlib.') or
                  m.startswith('Openmath.') or m.startswith('FormalConjecturesForMathlib.'))]
    return bad, opts, badopts, badimports


if __name__ == '__main__':
    flagged = False
    for p in sys.argv[1:]:
        bad, opts, badopts, badimports = scan(p)
        ok = not bad and not badopts and not badimports
        flagged |= not ok
        print(f"SRCSCAN {'ok' if ok else 'FLAG'} {p} forbidden={bad} set_options={opts} bad_options={badopts} "
              f"bad_imports={badimports}")
    sys.exit(1 if flagged else 0)
