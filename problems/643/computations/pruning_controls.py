from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import importlib.util,inspect,json,sys
if sys.flags.optimize:raise RuntimeError("Run without -O or -OO")
root=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('primary',root/'check_profiles.py');cp=importlib.util.module_from_spec(spec);spec.loader.exec_module(cp)
# Reuse only independently written formulas and predicates from preceding test by AST extraction.
import ast
source=Path(__file__).with_name('independent_audit.py').read_text();tree=ast.parse(source)
ns={'Q':Q};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ('S','F','admiss')],type_ignores=[]),'independent-formulas','exec'),ns)
rows=[];old=cp.mats;cp.N=3;cp.mats=lambda t:[m[:4,:4] for m in old(t)]
for t in [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,2,2),(0,2,3)]:
 vals=[ns['F'](x,t) for x in product(range(4),repeat=6) if ns['admiss'](x,t)]
 target=min(vals);low,count,eq=cp.cycle(t,target)
 assert eq==vals.count(target),(t,eq,vals.count(target));rows.append({'kind':'cycle-pruning','t':t,'target':str(target),'equalities':eq,'enumerated_candidates':count})
# Actual case3 body, only literal domain length 93 changed to 5; all pruning code unchanged.
space=dict(cp.__dict__);space.update({'p':cp.p[:5],'q':cp.q[:,:5],'rel':lambda a,b:cp.rel(a,b)[:5,:5]})
exec(inspect.getsource(cp.case3).replace('93','5'),space)
def W(x,t):
 ab,ba,ca,cb=x;a,b,c=t
 return Q(1,1+ca+cb+c)+Q(sum(t),6)+ns['S'](ba,ca,c)+ns['S'](ca,ba,b)+ns['S'](cb,ab,a)+ns['S'](ab,cb,c)+cp.kap(ab+a,a)+cp.kap(ba+b,b)
def ok(x,t,nonc):
 ab,ba,ca,cb=x;a,b,c=t
 feasible=((ba+b>0)==(ca+c>0) and (cb+c>0)==(ab+a>0))
 return feasible and (not nonc or (ca+cb!=1 or ab!=0) if a else not nonc or (ca+cb!=1 or ba!=0) if b else True) if sum(t)==1 else feasible
# Avoid conditional-expression precedence in oracle by explicit predicate.
def ok(x,t,nonc):
 ab,ba,ca,cb=x;a,b,c=t
 if ((ba+b>0)!=(ca+c>0)) or ((cb+c>0)!=(ab+a>0)):return False
 if not nonc:return True
 if a:return ca+cb!=1 or ab!=0
 if b:return ca+cb!=1 or ba!=0
 return True
for t,nonc in [((0,0,0),False),((1,0,0),False),((0,1,0),False),((0,0,1),False),((2,2,2),False),((0,2,3),False),((1,0,0),True),((0,1,0),True),((0,0,1),True)]:
 vals=[W(x,t) for x in product(range(5),repeat=4) if ok(x,t,nonc)];target=min(vals)
 low,count,eq=space['case3'](t,target,nonc)
 assert eq==vals.count(target),(t,nonc,eq,vals.count(target))
 rows.append({'kind':'tail-pruning-domain-constants-only','t':t,'noncompliant':nonc,'target':str(target),'equalities':eq,'enumerated_candidates':count})
print(json.dumps(rows,indent=2))
