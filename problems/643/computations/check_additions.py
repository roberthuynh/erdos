"""Exact finite-domain and host-example checks; not a universal host proof."""
from fractions import Fraction as F
from itertools import combinations,product,permutations
import json

def wbox():
    rows=[]
    for b,c,m,h in product(range(12),range(12),range(7),range(7)):
        if not 1<=m+h<=6:continue
        if m>0 and b==0 or h>0 and c==0:continue
        if c==0 and b>int(m>0) or b==0 and c>int(h>0):continue
        N=b+h
        beta=F(1,4)+F(1,2+N) if h==0 else F(1,6)+F(1,2+N)+F(1,2*(2+h))
        xb=F(int(m>0),2*(1+c+m))+F(b-int(m>0),2*(1+c))
        xc=F(int(h>0),2*(1+b+h))+F(c-int(h>0),2*(1+b))
        tau=(F(0) if m==0 else F(1,12) if m==1 else F(m,3*(m+3)))+F(int(h==1),12)
        gap=beta+xb+xc+F(m+h,6)-F(11,12)-tau
        assert gap>=0
        rows.append((gap,(b,c,m,h)))
    assert len(rows)==3279
    eq=[x for g,x in rows if g==0]; assert eq==[(1,0,1,0)]
    return {'points':len(rows),'minimum':str(min(g for g,_ in rows)),'equality':eq}

def relabel():
    rows=[]
    for p1,p2,p3 in permutations(['x','u','z']):
        base={p1,p2,p3}; r='r'; w='w'; s='s'
        H={frozenset({v,*p}) for v in [r,w,s] for p in combinations(base,2)}
        assert frozenset({p1,p2,s}) in H and frozenset({p1,p3,s}) in H
        rows.append([p1,p2,p3])
    return rows

def u2():
    count=0
    for k in range(20):
      for r in range(k+1,25):
       for j in range(r+1,30):
        for e in range(1,12):
         raw=F(e,2*(1+k))+F(k,2*(1+j+e))
         loss=F(1,2*(1+k))-F(1,2*(2+k))
         corrected=F(e-1,2*(1+k))+F(1,2*(2+k))+F(k,2*(1+j+e))
         assert raw-loss==corrected
         assert corrected>=F(1,2*(2+k))+F(k,2*(2+j))>=F(k,2*(1+j))
         assert F(1,2*(1+k))-F(k,2*(1+j+e)**2)>0
         count+=1
    return count

def partition():
    count=0
    for left,right,f,g in product(range(1,12),range(1,12),range(12),range(12)):
        compliant=((left==1)!=(right==1)) and (right!=1 or g==0) and (left!=1 or f==0)
        classes=(left>=2 and right>=2) or (left==right==1) or (right==1 and g>=1) or (left==1 and f>=1)
        assert classes== (not compliant); count+=1
    return count

def host_stats(H):
    H=set(map(frozenset,H)); V=set().union(*H) if H else set()
    pairs=list(map(frozenset,combinations(sorted(V),2)))
    links={p:{next(iter(e-p)) for e in H if p<=e} for p in pairs}
    cn={q:{p for p in pairs if not p&q and all(p|{x} in H for x in q)} for q in pairs}
    disjoint={}
    for e,f in combinations(H,2):
        if not e&f:disjoint.setdefault(e|f,[]).append((e,f))
    forbidden=any(len(v)>1 for v in disjoint.values())
    match=any(any(not p&r for p,r in combinations(ps,2)) for ps in cn.values())
    assert forbidden==match
    charges={};triangles={}
    for e in H:
        sig=sum((F(1,len(links[p])) for p in pairs if p<=e),F(0))
        opts=[frozenset((next(iter(e-p)),z)) for p in pairs if p<=e for z in links[p]-e]
        assert len(opts)==len(set(opts))
        tau=sum((F(1,2*len(cn[q])) for q in opts),F(0))
        charges[e]=sig+tau-2
        triangles[e]={q for q in opts if len(cn[q])==3 and len(set().union(*cn[q]))==3}
        if not forbidden:
            # Actual slots, with identities preserved across groups.
            ev=sorted(e);groups=[links[frozenset(e-{a})]-e for a in ev]
            for i,a in enumerate(ev):
              b,c=[v for v in ev if v!=a]
              for z in groups[i]:
                rb={s for s in links[frozenset((a,b))]-e if s!=z and frozenset((b,s,z)) in H}
                rc={s for s in links[frozenset((a,c))]-e if s!=z and frozenset((c,s,z)) in H}
                assert len(cn[frozenset((a,z))])==1+len(rb)+len(rc)
                if rb and rc:assert len(rb)==len(rc)==1 and rb==rc
    assert sum(charges.values(),F(0))==sum(bool(links[p]) for p in pairs)+sum(bool(cn[p]) for p in pairs)-2*len(H)
    if forbidden:return False,0,0
    deficient={e for e in H if charges[e]<0}
    active=set().union(*(triangles[e] for e in deficient)) if deficient else set()
    pots={q:F(0) for q in active};fin=charges.copy()
    for e in H:
        act=triangles[e]&active
        if charges[e]>0 and act:
            for q in act:pots[q]+=charges[e]/len(act)
            fin[e]=F(0)
    for q in active:
        receivers={e for e in deficient if q in triangles[e]};den=sum((-charges[e] for e in receivers),F(0))
        assert den>0
        for e in receivers:fin[e]+=pots[q]*(-charges[e])/den
    assert sum(fin.values(),F(0))==sum(charges.values(),F(0))
    for e in deficient:assert len(triangles[e])==1
    assert all(v>=0 for v in fin.values())
    return True,len(deficient),max((len(triangles[e]&active) for e in H),default=0)

def hosts():
    count=avoiding=defs=0; maxact=0
    E=list(combinations(range(5),3))
    cases=([E[i] for i in range(10) if mask>>i&1] for mask in range(1024))
    for H in cases:
        ok,d,act=host_stats(H);count+=1;avoiding+=ok;defs+=d;maxact=max(maxact,act)
    # All four-edge systems on six labelled vertices contain every minimal forbidden pattern.
    for H in combinations(list(combinations(range(6),3)),4):
        ok,d,act=host_stats(H);count+=1;avoiding+=ok;defs+=d;maxact=max(maxact,act)
    # Deficient family from §3.2, includes genuinely negative initial charges.
    for p,q in [(10,10),(12,15),(23,23)]:
        a,b,c,w,t=0,1,2,3,4;Z=list(range(5,5+p-1));X=list(range(5+p-1,5+p-1+q));A=[w]+Z
        H=[(a,b,c),(a,c,w),(a,b,t),(a,t,w),(b,t,w)]+[(b,c,z) for z in A]+[(a,b,x) for x in X]+[(b,x,z) for x in X for z in A]
        ok,d,act=host_stats(H);assert ok;count+=1;avoiding+=ok;defs+=d;maxact=max(maxact,act)
        if (p,q)==(10,10):assert d>0
    assert defs>0
    witness=[(0,i,j) for i in [1,2] for j in [3,4,5,6]]
    assert host_stats(witness)[0] and all(0 in e for e in witness)
    return {'hosts':count,'avoiding':avoiding,'deficient_triples_checked':defs,'max_active_incidence_observed':maxact,'witness_edges':8,'limit':'bounded corroboration only; does not prove universal host or multi-active-anchor cases'}

print(json.dumps({'result':'PASS','wbox':wbox(),'six_relabellings':relabel(),'u2_points':u2(),'partition_points':partition(),'hosts':hosts()},indent=2))
