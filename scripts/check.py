#!/usr/bin/env python3
"""Run registered problem checks; every subprocess has a 240-second bound."""
import argparse
import datetime
import hashlib
import heapq
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def inside(root, value, directory=False):
    if not isinstance(value, str) or not value or '\\' in value:
        raise ValueError('Invalid relative path')
    part = PurePosixPath(value)
    if part.is_absolute() or '..' in part.parts or str(part) != value:
        raise ValueError('Invalid relative path')
    path = root / value
    if any(p.is_symlink() for p in [path, *path.parents] if p == root or root in p.parents):
        raise ValueError('Symlinks are not permitted in registered paths')
    if not path.resolve().is_relative_to(root.resolve()):
        raise ValueError('Path escapes root')
    if not (path.is_dir() if directory else path.is_file()):
        raise ValueError(f'Missing registered path: {value}')
    return path


def load_registry(root=ROOT):
    data = json.loads((root / 'problems.json').read_text())
    if data.get('schema_version') != 1 or not isinstance(data.get('problems'), list) or not data['problems']:
        raise ValueError('Invalid or empty problem registry')
    result = {}
    for item in data['problems']:
        identifier = item.get('id')
        if not isinstance(identifier, str) or not re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', identifier) or identifier in result:
            raise ValueError('Invalid or duplicate problem ID')
        if item.get('path') != f'problems/{identifier}':
            raise ValueError('Problem path must match its ID')
        package = inside(root, item['path'], directory=True)
        for field in ['README.md', 'RESULTS.md']:
            inside(package, field)
        if not isinstance(item.get('title'), str) or not item['title'].strip() or not isinstance(item.get('topics'), list) or not item['topics'] or not all(isinstance(t,str) and t.strip() for t in item['topics']):
            raise ValueError('Problem title and topics required')
        checks = item.get('checks', {})
        if set(checks) != {'docs', 'full'}:
            raise ValueError('Both docs and full check modes must be declared')
        for commands in checks.values():
            if not isinstance(commands,list) or not commands:
                raise ValueError('Check mode cannot be empty')
            for cmd in commands:
                if not isinstance(cmd,list) or len(cmd)<3 or cmd[:2]!=['python3','-B'] or not all(isinstance(a,str) and a for a in cmd):
                    raise ValueError('Checks must be explicit python3 -B script commands')
                inside(package, cmd[2])
        if 'lean' in item:
            lean = item['lean']
            if not isinstance(lean,dict) or set(lean)!={'registry','coverage','axioms','replay','oracle','target'}:
                raise ValueError('Incomplete Lean verification configuration')
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', lean['target']):
                raise ValueError('Invalid Lean target')
            for key,value in lean.items():
                if key != 'target': inside(package,value)
            for value in ['lean-toolchain','lakefile.toml','lake-manifest.json']: inside(package,value)
        phased_plans(item, root)
        result[identifier] = item
    actual = {p.name for p in (root/'problems').iterdir() if p.is_dir()}
    if actual != set(result):
        raise ValueError('Unregistered or missing problem directory')
    return result


def phased_plans(item, root):
    entries = item.get('phased_lean', [])
    if not isinstance(entries, list): raise ValueError('Invalid phased Lean project list')
    result=[]; seen=set(); package=root/item['path']
    for cfg in entries:
        if not isinstance(cfg,dict) or set(cfg)!={'path','plan','profile'}:
            raise ValueError('Incomplete phased Lean project')
        if not all(isinstance(v,str) and v for v in cfg.values()) or cfg['path'] in seen:
            raise ValueError('Invalid or duplicate phased Lean project')
        seen.add(cfg['path']); inside(package,cfg['path'],directory=True)
        plan=json.loads(inside(package,cfg['plan']).read_text())
        if (set(plan)!={'schema','profile','target','modules','build_chunk','kernel_chunk'}
                or plan['schema']!=1 or plan['profile']!=cfg['profile']
                or not isinstance(plan['target'],str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',plan['target'])
                or any(type(plan[k]) is not int or not 1<=plan[k]<=10000 for k in ['modules','build_chunk','kernel_chunk'])):
            raise ValueError('Invalid phased Lean command plan')
        for name in ['tools/setup.py','tools/run_phase.py','check.sh']:
            inside(package,cfg['path']+'/'+name)
        result.append((cfg,plan))
    return result


def lean_imports(text):
    """Read import lines after masking nested comments and escaped strings."""
    masked=[]; i=0; depth=0; string=False
    while i < len(text):
        pair=text[i:i+2]; char=text[i]
        if depth:
            if pair=='/-': depth+=1; masked.extend('  '); i+=2
            elif pair=='-/': depth-=1; masked.extend('  '); i+=2
            else: masked.append('\n' if char=='\n' else ' '); i+=1
        elif string:
            if char=='\\': masked.extend('  '); i+=2
            elif char=='"': string=False; masked.append(' '); i+=1
            else: masked.append('\n' if char=='\n' else ' '); i+=1
        elif pair=='/-': depth=1; masked.extend('  '); i+=2
        elif pair=='--':
            end=text.find('\n',i)
            if end<0: end=len(text)
            masked.extend(' '*(end-i)); i=end
        elif char=='"': string=True; masked.append(' '); i+=1
        else: masked.append(char); i+=1
    if depth or string: raise ValueError('Unterminated Lean comment or string')
    imports=[]
    for line in ''.join(masked).splitlines():
        match=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$',line)
        if match:
            names=match.group(1).split()
            if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',name) for name in names):
                raise ValueError('Unsupported Lean import syntax')
            imports.extend(names)
    return imports


def build_order(package, modules, target):
    """Order exactly the configured local DAG, with dependencies before importers."""
    if not modules or len(modules)!=len(set(modules)):
        raise ValueError('Empty or duplicate configured modules')
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',m) for m in modules):
        raise ValueError('Invalid module list')
    configured=set(modules)
    if target not in configured: raise ValueError('Build root is not configured')
    dependencies={}
    for module in sorted(configured):
        source=inside(package,module.replace('.','/')+'.lean')
        dependencies[module]=set()
        for imported in lean_imports(source.read_text()):
            if imported in configured: dependencies[module].add(imported)
            elif (package/(imported.replace('.','/')+'.lean')).exists():
                raise ValueError(f'Unconfigured local import: {imported}')
    # Requiring every other module before the aggregate also detects a child
    # importing the aggregate instead of silently breaking dependency order.
    dependencies[target].update(configured-{target})
    users={m:set() for m in configured}
    for module,deps in dependencies.items():
        for dependency in deps: users[dependency].add(module)
    ready=[m for m,deps in dependencies.items() if not deps]; heapq.heapify(ready)
    result=[]
    while ready:
        module=heapq.heappop(ready); result.append(module)
        for user in sorted(users[module]):
            dependencies[user].remove(module)
            if not dependencies[user]: heapq.heappush(ready,user)
    if len(result)!=len(configured): raise ValueError('Cycle in configured Lean imports')
    return result


def execute(cmd, cwd, log, run=subprocess.run):
    with log.open('w') as stream:
        try:
            result=run(['timeout','--signal=INT','--kill-after=5','240',*cmd],cwd=cwd,stdout=stream,stderr=subprocess.STDOUT,
                       env={**os.environ,'LEAN_NUM_THREADS':'2','PYTHONDONTWRITEBYTECODE':'1'},timeout=250)
            return 124 if result.returncode in {124,137} else result.returncode
        except subprocess.TimeoutExpired:
            stream.write('\nUNKNOWN: command exceeded 240 seconds\n')
            return 124


def run_problem(item, mode, output, root=ROOT, run=subprocess.run):
    package=root/item['path']; output.mkdir(parents=True,exist_ok=True)
    records=[]
    def invoke(cmd, label, require=None):
        log=output/f'{len(records):04d}-{label}.log'
        print(f"{item['id']}: {label}",flush=True)
        code=execute(cmd,package,log,run)
        text=log.read_text()
        status='UNKNOWN' if code==124 else ('PASS' if code==0 and (require is None or require in text) else 'FAIL')
        records.append({'command':cmd,'status':status,'returncode':code,'log':log.name,'sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
        receipt={'problem':item['id'],'mode':mode,'status':status if status!='PASS' else 'RUNNING','updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':records}
        (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        if status!='PASS': raise RuntimeError(f'{status}: {label}; see {log}')
        return text
    for cmd in item['checks'][mode]:invoke(cmd,Path(cmd[2]).stem)
    if mode=='full' and 'lean' in item:
        cfg=item['lean']
        modules=invoke(['python3','-B',cfg['coverage'],'--list'],'modules').splitlines()
        # Each bounded build now has its configured local dependencies built.
        for module in build_order(package,modules,cfg['target']):
            invoke(['lake','build',module],'build-'+module)
        invoke(['python3','-B',cfg['axioms']],'axioms',require='STATEMENTS: PASS')
        entries=json.loads((package/cfg['registry']).read_text())
        for entry in entries:
            if entry['oracle']:
                invoke(['bash',cfg['oracle'],entry['module'].replace('.','/')+'.lean',entry['declaration']],
                       'oracle-'+entry['declaration'],require='RESULT: PASS')
        for module in modules:
            invoke(['python3','-B',cfg['replay'],'--module',module],'replay-'+module,require='KERNEL REPLAY: PASS')
    if mode=='full':
        for project,plan in phased_plans(item,root):
            prefix=project['path']; invoke(['python3','-B',prefix+'/tools/setup.py'],'phased-setup')
            runner=['python3','-B',prefix+'/tools/run_phase.py']
            invoke(runner+['prepare'],'phased-prepare')
            for i in range((plan['modules']+plan['build_chunk']-1)//plan['build_chunk']):
                invoke(runner+['build',str(i)],'phased-build-'+str(i))
            invoke(runner+['hygiene'],'phased-hygiene')
            for i in range((plan['modules']+plan['kernel_chunk']-1)//plan['kernel_chunk']):
                invoke(runner+['kernel',str(i)],'phased-kernel-'+str(i))
            invoke(runner+['finalize'],'phased-finalize',require='RESULT: PASS')
    receipt=json.loads((output/'receipt.json').read_text());receipt['status']='PASS'
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(f"{item['id']} {mode}: PASS; receipt {output/'receipt.json'}")
    return records


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--problem',required=True)
    parser.add_argument('--mode',choices=['docs','full'],default='docs')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    from check_collection import check_collection
    check_collection()
    registry=load_registry()
    if args.problem not in registry:raise ValueError('Unknown problem ID')
    output=args.output or Path(tempfile.mkdtemp(prefix=f'erdos-{args.problem}-{args.mode}-'))
    run_problem(registry[args.problem],args.mode,output)

if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError,RuntimeError) as error:
        print(f'CHECK: {error}',file=sys.stderr);sys.exit(1)
