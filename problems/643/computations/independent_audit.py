"""Independent manuscript formulas, exhaustive small domains, negative controls."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import importlib.util,sys,json,hashlib
if sys.flags.optimize:raise RuntimeError('Run without -O or -OO')
PKG=Path(__file__).resolve().parent
def load(name):
    spec=importlib.util.spec_from_file_location(name,PKG/(name+'.py')); m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
cp=load('check_profiles'); ci=load('c1_integer')
def S(p,q,y):return Q(p*p,2*(p*(q+1)+y)) if p else Q(0)
def F(x,t):
    ab,ac,bc,ba,ca,cb=x;a,b,d=t
    return (Q(1,ab+ac+a+1)+Q(1,bc+ba+b+1)+Q(1,ca+cb+d+1)+Q(sum(t),6)+S(ac,bc,b)+S(bc,ac,a)+S(ba,ca,d)+S(ca,ba,b)+S(cb,ab,a)+S(ab,cb,d))
def admiss(x,t):
    ab,ac,bc,ba,ca,cb=x;a,b,d=t
    return ((ac+a>0)==(bc+b>0) and (ba+b>0)==(ca+d>0) and (cb+d>0)==(ab+a>0))
def cls_member(x,t,pos,cls):
    ab,ac,bc,ba,ca,cb=x;g=[ab,bc,ca];f=[ac,ba,cb];n=[g[i]+f[i]+t[i] for i in range(3)]
    l=(pos+1)%3;r=(pos-1)%3
    return g[l]>=1 and f[r]>=1 and {1:n[l]>=2 and n[r]>=2,2:n[l]==n[r]==1,3:n[r]==1 and g[pos]>=1,4:n[l]==1 and f[pos]>=1}[cls]
def min_cycle(mats):
    d=mats[0]
    for e in mats[1:]:d=cp.mp(d,e)
    return int(cp.np.diag(d).min())
def mask_matrices(t,pos,cls):
    # Literal translation of source masks, compared below to direct logical membership.
    M=cp.mats(t);p,q=cp.p,cp.q;nx=(pos+1)%3;pv=(pos-1)%3
    M[2*nx]=cp.np.where(p>=1,M[2*nx],cp.INF);M[2*pv]=cp.np.where(q>=1,M[2*pv],cp.INF)
    for k,cond in ({nx:p+q>=2,pv:p+q>=2} if cls==1 else {nx:p+q==1,pv:p+q==1} if cls==2 else {pv:p+q==1,pos:p>=1} if cls==3 else {nx:p+q==1,pos:q>=1}).items():M[2*k]=cp.np.where(cond,M[2*k],cp.INF)
    return M
out={'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [PKG/'check_profiles.py',PKG/'c1_integer.py']},'tests':[]}
# Compare BOTH implementations' formulas and matrix constraints to independent manuscript code.
checks=0;maskchecks=0
triples=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,0,0),(0,2,3),(2,2,2),(0,0,11)]
for t in triples:
    M=cp.mats(t);J=ci.matrices(2,t);best=None;imin=None
    for x in product(range(3),repeat=6):
        ok=admiss(x,t);raw=sum(int(M[i][x[i],x[(i+1)%6]]) for i in range(6))
        assert (raw<cp.INF)==ok
        assert ci.feasible(x,t)==ok
        assert cp.exact(x,t)==ci.exact(x,t)==F(x,t)
        if ok:
            enclosed=Q(raw,cp.SCALE)+Q(sum(t),6);assert enclosed<=F(x,t)
            v=sum(J[i][x[i]][x[(i+1)%6]] for i in range(6))+ci.floor(Q(sum(t),6));assert Q(v,ci.SCALE)<=F(x,t)
            best=F(x,t) if best is None else min(best,F(x,t));imin=raw if imin is None else min(imin,raw)
        checks+=1
    assert min_cycle([m[:3,:3] for m in M])==imin
    out['tests'].append({'kind':'small_profile_oracle','t':t,'domain':'0..2^6','minimum':str(best)})
for pos in range(3):
    t=tuple(int(i==pos) for i in range(3));M=[mask_matrices(t,pos,j) for j in range(1,5)]
    for x in product(range(4),repeat=6):
        for j,mats in enumerate(M,1):
            got=sum(int(mats[i][x[i],x[(i+1)%6]]) for i in range(6))<cp.INF
            assert got==(admiss(x,t) and cls_member(x,t,pos,j)),(pos,j,x);maskchecks+=1
out['profile_checks']=checks;out['class_mask_checks']=maskchecks
# Tail: independent rational scan, extra p=161..400 checks, and decomposed matrices.
def kap(u,s):return min([Q(0)]+[Q((p+1)**2-(u+s)*(p+1)-s*u,2*(p+1)**2*(p+1+u)) for p in range(23,161)])
for u in range(104):
 for s in range(12):
    v=kap(u,s);assert cp.kap(u,s)==v
    assert 161**2-(u+s)*161-s*u>0 and 322-u-s>0
    for p in (161,162,200,400,10000):assert Q((p+1)**2-(u+s)*(p+1)-s*u,2*(p+1)**2*(p+1+u))>=v
out['tail_pairs']=104*12
rchecks=0
for t in triples:
 a,b,d=t;A=cp.rel(b,d).T;B=cp.rel(d,a)
 for ab,ba,ca,cb in product(range(5),repeat=4):
    ok=((ba+b>0)==(ca+d>0) and (cb+d>0)==(ab+a>0))
    assert (int(A[ca,ba])+int(B[cb,ab])<cp.INF)==ok
    if ok:
      val=Q(1,1+ca+cb+d)+Q(sum(t),6)+S(ba,ca,d)+S(ca,ba,b)+S(cb,ab,a)+S(ab,cb,d)+kap(ab+a,a)+kap(ba+b,b)
      low=Q(cp.SCALE//(1+ca+cb+d)+cp.floorf(Q(sum(t),6))+int(A[ca,ba])+int(B[cb,ab])+cp.floorf(cp.kap(ab+a,a))+cp.floorf(cp.kap(ba+b,b)),cp.SCALE)
      assert low<=val
    for nonc in (False,True):
      if nonc and sum(t)==1:
        sourceok=ok and (not a or cb>=1) and (not b or ca>=1) and (not a or ca+cb!=1 or ab>=1) and (not b or ca+cb!=1 or ba>=1)
        directok=ok and ((ca+cb!=1 or ab!=0) if a else (ca+cb!=1 or ba!=0) if b else True)
        assert sourceok==directok
    rchecks+=1
out['rest_checks']=rchecks
# Entire anchor box, entirely independent rational formula; remove constraints as negative controls.
def gap(b,c,m,h):
 N=b+h
 beta=Q(1,4)+Q(1,N+2) if h==0 else Q(1,6)+Q(1,N+2)+Q(1,2*(h+2))
 xb=Q(int(m>=1),2*(1+c+m))+Q(b-int(m>=1),2*(1+c))
 xc=Q(int(h>=1),2*(1+b+h))+Q(c-int(h>=1),2*(1+b))
 tau=Q(int(h==1),12) if m==0 else Q(1,6) if m==h==1 else Q(1,12) if m==1 else Q(m,3*(m+3))+Q(int(h==1),12)
 return beta+xb+xc+Q(m+h,6)-Q(11,12)-tau
points=[];neg=[]
for b,c,m,h in product(range(12),range(12),range(7),range(7)):
 if not 1<=m+h<=6:continue
 ok=(not m or b>=1) and (not h or c>=1) and (c!=0 or b<=int(m>=1)) and (b!=0 or c<=int(h>=1))
 g=gap(b,c,m,h)
 if ok:points.append(((b,c,m,h),g));assert g>=0
 elif g<0:neg.append(((b,c,m,h),str(g)))
assert len(points)==3279 and [x for x,g in points if g==0]==[(1,0,1,0)]
out['wbox']={'count':len(points),'minimum':str(min(g for x,g in points)),'equality':[x for x,g in points if g==0],'constraint_removal_negative_examples':neg[:5],'removed_negative_count':len(neg)}
# Exact bound vs minima/equality distinction and sentinel guard.
listed=[((0,92,92,0,0,1),(1,0,0)),((92,0,1,0,0,92),(1,0,0))]
assert all(F(x,t)==Q(288336581,149610588) for x,t in listed)
out['numeric_safety']={'largest_S_numerator':92**2*cp.SCALE,'int64_max':2**63-1,'six_INF':6*cp.INF,'finite_path_ceiling':300*cp.SCALE}
# Strengthen false targets in tightly bounded domain using matrix slicing and temporary N.
oldN=cp.N;oldm=cp.mats;cp.N=2;cp.mats=lambda t:[m[:3,:3] for m in oldm(t)]
try:
 try:cp.cycle((0,0,0),Q(4))
 except AssertionError as e:out['false_target_control']={'detected':True,'exception':str(e)}
 else:raise AssertionError('false target accepted')
finally:cp.N=oldN;cp.mats=oldm
print(json.dumps(out,indent=2))
