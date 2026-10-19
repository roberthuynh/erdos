"""Generate explicit labelled finite hosts from the displayed constructions."""
from itertools import combinations,product
from pathlib import Path
import json,sys

def da2():
    classes={v:[v] for v in ('a','b','c','w','t','r','z')}
    classes.update({name:[f'{name}{i:02}' for i in range(size)] for name,size in [('X',9),('Z',26),('E',19),('Y',17)]})
    patterns=[list(s) for s in ['abc','acw','abt','atw','btw','bcw','bcr','brz','crz','cwz','bwz','abz','abX','bXw','bcZ','bXZ','abE','bEr','bEZ','bzZ','bwY','bYZ']]
    edges={tuple(sorted(edge)) for pattern in patterns for edge in product(*(classes[v] for v in pattern))}
    return {'name':'DA2(9,26,19,17)','classes':classes,'patterns':patterns,'vertices':sorted(v for group in classes.values() for v in group),'edges':[list(e) for e in sorted(edges)]}

def cone(k):
    base=['b0','b1','b2'];apex=[f'x{i}' for i in range(k)]
    edges=sorted(tuple(sorted((*pair,x))) for pair in combinations(base,2) for x in apex)
    return {'name':f'cone_{k}','base':base,'apexes':apex,'vertices':base+apex,'edges':[list(e) for e in edges]}

if __name__=='__main__':
    if len(sys.argv)!=2:raise SystemExit('Usage: generate_examples.py <NEW_OUTPUT_DIRECTORY>')
    out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=False)
    for name,host in [('da2-host.json',da2()),('cone3-host.json',cone(3)),('cone4-host.json',cone(4))]:
        (out/name).write_text(json.dumps(host,indent=2)+'\n')
