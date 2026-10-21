"""Synthetic expanded scope rejection controls; no proof execution."""
import json
from pathlib import Path
import tempfile
from design_scope import load_scope
with tempfile.TemporaryDirectory(prefix='643-design-scope-') as td:
    root=Path(td)
    baseline={'schema':1,'configured':True,'target':'Openmath.Final',
              'declarations':{'Final.exists':'Openmath.Final','Final.equality':'Openmath.Final'},
              'module_lean_flags':{'Openmath.Decide281':['-DmaxHeartbeats=0','-DmaxRecDepth=100000']},
              'limitations':['Human review outstanding.']}
    p=root/'design-scope.json';p.write_text(json.dumps(baseline))
    assert load_scope(root)==baseline
    for key,value in [('configured',False),('declarations',{}),('target','bad target'),
                      ('module_lean_flags',{'Openmath.Final':['-Ddebug.skipKernelTC=true']})]:
        p.write_text(json.dumps({**baseline,key:value}))
        try:load_scope(root)
        except RuntimeError:print(key+': REJECTED')
        else:raise AssertionError(key)
print('PASS_SCOPE_CONTROLS_ONLY')
