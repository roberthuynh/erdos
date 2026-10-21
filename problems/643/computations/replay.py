"""Replay finite checks into a new directory; failures never create success receipts."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time

COMMANDS=[['check_profiles.py','box'],['check_profiles.py','tail'],['crosscheck_profiles.py'],['check_wbox.py'],['c1_integer.py'],['check_additions.py']]

def semantic(value):
    """Remove timing fields only; preserve all mathematical output and ordering."""
    if isinstance(value,dict):
        return {k:semantic(v) for k,v in value.items() if k not in {'seconds','elapsed_seconds'}}
    if isinstance(value,list):return [semantic(v) for v in value]
    return value

def semantic_hash(value):
    return hashlib.sha256(json.dumps(semantic(value),sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()

def text(value):
    if value is None:return ''
    return value.decode('utf-8',errors='replace') if isinstance(value,bytes) else value

def main():
    if sys.flags.optimize:
        raise RuntimeError('Optimized Python is unsupported; run without -O or -OO')
    root=Path(__file__).resolve().parent
    out=Path(sys.argv[1] if len(sys.argv)>1 else 'replay-output').absolute()
    # Exclusive creation rejects even empty existing directories and symlinks.
    out.mkdir(parents=True,exist_ok=False)
    rows=[]
    try:
        manifest=json.loads((root/'SHA256.json').read_text())
        for name,digest in manifest.items():
            if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
                raise ValueError(f'Source hash mismatch: {name}')
        for i,args in enumerate(COMMANDS):
            start=time.monotonic()
            if args[0]=='crosscheck_profiles.py':
                command=[sys.executable,'-I','-c',"import sys,runpy;sys.path.insert(0,sys.argv[1]);runpy.run_path(sys.argv[2],run_name='__main__')",str(root),str(root/args[0])]
            else:command=[sys.executable,'-I',str(root/args[0]),*args[1:]]
            row={'command':command,'cwd':str(root),'timeout_seconds':240,'isolated_python':True}
            try:
                run=subprocess.run(command,capture_output=True,text=True,timeout=240,cwd=root)
            except subprocess.TimeoutExpired as exc:
                (out/f'{i}-{args[0]}.stdout').write_text(text(exc.stdout))
                (out/f'{i}-{args[0]}.stderr').write_text(text(exc.stderr))
                row.update(seconds=time.monotonic()-start,returncode=None,status='UNKNOWN_TIMEOUT')
                rows.append(row)
                raise
            (out/f'{i}-{args[0]}.stdout').write_text(run.stdout)
            (out/f'{i}-{args[0]}.stderr').write_text(run.stderr)
            row.update(seconds=time.monotonic()-start,returncode=run.returncode)
            rows.append(row)
            if run.returncode!=0:raise RuntimeError(f'Checker failed: {args}: exit {run.returncode}')
            row['semantic_sha256']=semantic_hash(json.loads(run.stdout))
        import numpy
        receipt={'result':'PASS','scope':'Six finite computations only; not full-theorem verification','python':sys.version,'numpy':numpy.__version__,'platform':platform.platform(),'commands':rows}
        (out/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps({'result':'PASS','checks':len(rows),'output':str(out)}))
        return 0
    except Exception as exc:
        failure={'result':'UNKNOWN' if isinstance(exc,subprocess.TimeoutExpired) else 'FAIL','error_type':type(exc).__name__,'error':str(exc),'commands':rows,'success_receipt_created':False}
        (out/'failure.json').write_text(json.dumps(failure,indent=2)+'\n')
        print(json.dumps(failure),file=sys.stderr)
        return 2

if __name__=='__main__':raise SystemExit(main())
