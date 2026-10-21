"""Integer-enclosure check of the stated finite profile inequalities.
All numerical pruning uses exact int64 arithmetic, no floating point.
SCALE floors each rational summand. Six min-plus matrices give lower bounds.
Every cycle whose lower bound is <= target is enumerated and tested with Fraction.
N=92, t<=11 require the analytic reductions in the accompanying proof.
"""
from fractions import Fraction as F
from functools import lru_cache
import itertools, json, sys, time
import numpy as np
N=92; SCALE=2**40; INF=2**58
EQUALITY_VECTORS=[]
p=np.arange(N+1,dtype=np.int64)[:,None]; q=p.T
# Largest numerator SCALE*92**2 < 2**54; every finite path < 300*SCALE.
# Six INF sentinels < 2**61, safely below signed int64 overflow.
def floorf(x): return x.numerator*SCALE//x.denominator
S=[]
for t in range(12):
    den=2*(p+p*q+t)
    S.append(np.where(p==0,0,(p*p*SCALE)//np.maximum(den,1)))
def rel(a,b): return np.where((p+a>0)==(q+b>0),S[b]+S[a].T,INF)
def mats(t):
    a,b,c=t
    return [SCALE//(1+p+q+a),rel(a,b),SCALE//(1+p+q+b),rel(b,c),SCALE//(1+p+q+c),rel(c,a)]
def mp(a,b): return np.min(a[:,:,None]+b[None,:,:],axis=1)
def sx(a,b,c): return F(a*a,2*(a+a*b+c)) if a else F(0)
def exact(x,t):
    ab,ac,bc,ba,ca,cb=x; a,b,c=t
    return (F(1,1+ab+ac+a)+F(1,1+bc+ba+b)+F(1,1+ca+cb+c)+F(a+b+c,6)
      +sx(ac,bc,b)+sx(bc,ac,a)+sx(ba,ca,c)+sx(ca,ba,b)+sx(cb,ab,a)+sx(ab,cb,c))
def cycle(t,target,cls=None,pos=0):
    M=mats(t)
    if cls:
        nx=(pos+1)%3; pv=(pos-1)%3
        M[2*nx]=np.where(p>=1,M[2*nx],INF)
        M[2*pv]=np.where(q>=1,M[2*pv],INF)
        for k,cond in ({nx:p+q>=2,pv:p+q>=2} if cls==1 else
                        {nx:p+q==1,pv:p+q==1} if cls==2 else
                        {pv:p+q==1,pos:p>=1} if cls==3 else
                        {nx:p+q==1,pos:q>=1}).items():
            M[2*k]=np.where(cond,M[2*k],INF)
    tail=[None]*6; tail[5]=M[5]
    for k in range(4,0,-1): tail[k]=mp(M[k],tail[k+1])
    constant=floorf(F(sum(t),6)); lim=floorf(target)-constant
    low=int(np.min(M[0]+tail[1].T))+constant
    count=0; equal=0
    def walk(path,total):
        nonlocal count,equal
        k=len(path)-1
        if k==5:
            if total+int(M[5][path[5],path[0]])<=lim:
                val=exact(path,t); count+=1
                assert val>=target,(path,t,str(val),str(target))
                equal+=val==target
                if val==target:
                    EQUALITY_VECTORS.append({"kind":"cycle","types":list(t),"coordinates":list(path),"coordinate_order":["ab","ac","bc","ba","ca","cb"],"target":str(target),"class":cls,"position":pos})
            return
        options=np.where(total+M[k][path[-1],:]+tail[k+1][:,path[0]]<=lim)[0]
        for v in options: walk(path+[int(v)],total+int(M[k][path[-1],v]))
    for v in range(N+1):
        if int(np.min(M[0][v,:]+tail[1][:,v]))<=lim: walk([v],0)
    return low,count,equal
@lru_cache(None)
def kap(u,t):
    # Positive numerator for x>160 for u<=103,t<=11; increasing thereafter.
    assert 161**2-(u+t)*161-t*u>0 and 322>u+t
    return min([F(0)]+[F(1,1+r+u)-F(1,2*(1+r))-F(t,2*(1+r)**2) for r in range(23,161)])
def case3(t,target,nonc=False):
    a,b,c=t
    ka=[kap(i+a,a) for i in range(93)]; kb=[kap(i+b,b) for i in range(93)]
    # rows outer (ca or cb); columns inner (ba or ab)
    A=rel(b,c).T+np.array([floorf(v) for v in kb])[None,:]
    B=rel(c,a)+np.array([floorf(v) for v in ka])[None,:]
    va=np.min(A,axis=1); vb=np.min(B,axis=1)
    va1=np.min(A[:,1:],axis=1); vb1=np.min(B[:,1:],axis=1)
    base=SCALE//(1+p+q+c)+floorf(F(sum(t),6))
    av=np.broadcast_to(va[:,None],(93,93)).copy(); bv=np.broadcast_to(vb[None,:],(93,93)).copy()
    ok=np.ones((93,93),dtype=bool)
    if nonc and a:
        ok=np.broadcast_to((q>=1)&(p+q>=1),(93,93)); bv=np.where(p+q==1,vb1[None,:],bv)
    if nonc and b:
        ok=np.broadcast_to((p>=1)&(p+q>=1),(93,93)); av=np.where(p+q==1,va1[:,None],av)
    lower=np.where(ok,base+av+bv,INF); lim=floorf(target); count=equal=0
    for ca,cb in zip(*np.where(lower<=lim)):
        ca=int(ca);cb=int(cb)
        amin=1 if nonc and b and ca+cb==1 else 0
        bmin=1 if nonc and a and ca+cb==1 else 0
        for ba in range(amin,93):
            rem=lim-int(base[ca,cb])-int(A[ca,ba])
            for ab in np.where(B[cb,bmin:]<=rem)[0]+bmin:
                ab=int(ab);count+=1
                val=(F(1,1+ca+cb+c)+F(sum(t),6)+sx(ba,ca,c)+sx(ca,ba,b)+sx(cb,ab,a)+sx(ab,cb,c)+ka[ab]+kb[ba])
                assert val>=target,(t,ab,ba,ca,cb,str(val),str(target))
                equal+=val==target
                if val==target:
                    EQUALITY_VECTORS.append({"kind":"tail","types":list(t),"coordinates":[ab,ba,ca,cb],"coordinate_order":["ab","ba","ca","cb"],"target":str(target),"noncompliant":nonc})
    return int(np.min(lower)),count,equal
if __name__=='__main__':
    mode=sys.argv[1]; start=time.time(); rows=[]
    triples=[t for t in itertools.product(range(12),repeat=3) if sum(t)<=11]
    if mode=='box':
        for t in triples:
            target=F(2) if sum(t)>=2 else F(23,12)
            rows.append((t,str(target),cycle(t,target)))
        for pos in range(3):
            t=tuple(int(i==pos) for i in range(3))
            for cls in range(1,5): rows.append((t,'noncompliant-'+str(cls),cycle(t,F(2),cls,pos)))
    elif mode=='tail':
        for t in triples: rows.append((t,'all',case3(t,F(1) if sum(t)>=2 else F(11,12))))
        for t in [(1,0,0),(0,1,0),(0,0,1)]: rows.append((t,'noncompliant',case3(t,F(1),True)))
    else: raise ValueError(mode)
    print(json.dumps({'mode':mode,'scale':SCALE,'cases':len(rows),'exact_candidates':sum(r[2][1] for r in rows),'equality':sum(r[2][2] for r in rows),'seconds':time.time()-start,'rows':rows,'target_equality_vectors':EQUALITY_VECTORS}))
