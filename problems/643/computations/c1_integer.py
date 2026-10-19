"""C1 t<=1: standalone integer lower bound from the manuscript formula.
No imports from earlier checkers, no NumPy, no floating point in decisions.
Vertices of a six-cycle are ab,ac,bc,ba,ca,cb; alternating edges
carry group reciprocals and relation terms. Feasibility is a missing edge.
Each term is floored at 2**32. Min-plus elimination finds the least closed
walk. Python integers cannot overflow. Output bounds certify all profiles.
This is a new implementation, not a blind independent mathematical review.
"""
from fractions import Fraction as F
from itertools import product
import json
SCALE=2**32

def sf(p,q,t):
    return F(p*p,2*(p+p*q+t)) if p else F(0)
def exact(x,t):
    ab,ac,bc,ba,ca,cb=x; a,b,c=t
    return sum((F(1,1+ab+ac+a),F(1,1+bc+ba+b),F(1,1+ca+cb+c),F(a+b+c,6),sf(ac,bc,b),sf(bc,ac,a),sf(ba,ca,c),sf(ca,ba,b),sf(cb,ab,a),sf(ab,cb,c)))
def feasible(x,t):
    ab,ac,bc,ba,ca,cb=x; a,b,c=t
    return ((ac+a>0)==(bc+b>0) and (ba+b>0)==(ca+c>0) and (cb+c>0)==(ab+a>0))
def floor(v): return v.numerator*SCALE//v.denominator

def matrices(n,t):
    a,b,c=t; mats=[]
    # Each relation entry floors the SUM of its two rational terms.
    for group,other in [(a,b),(b,c),(c,a)]:
        mats.append([[floor(F(1,1+i+j+group)) for j in range(n+1)] for i in range(n+1)])
        mats.append([[floor(sf(i,j,other)+sf(j,i,group)) if (i+group>0)==(j+other>0) else None for j in range(n+1)] for i in range(n+1)])
    return mats

def solve(n,t):
    mats=matrices(n,t); d=mats[0]; size=n+1
    for edge in mats[1:]:
        cols=list(zip(*edge)); new=[]
        for row in d:
            entries=[(k,v) for k,v in enumerate(row) if v is not None]
            out=[]
            for col in cols:
                vals=[v+col[k] for k,v in entries if col[k] is not None]
                out.append(min(vals) if vals else None)
            new.append(out)
        d=new
    return min(d[i][i] for i in range(size) if d[i][i] is not None)+floor(F(sum(t),6))

def main():
    tests=[]
    for t in [(0,0,0),(1,0,0),(0,1,0),(0,0,1)]:
        mats=matrices(3,t); brute=None; cnt=0
        for x in product(range(4),repeat=6):
            if not feasible(x,t): continue
            cnt+=1
            val=sum(mats[i][x[i]][x[(i+1)%6]] for i in range(6))+floor(F(sum(t),6))
            assert F(val,SCALE)<=exact(x,t)
            brute=val if brute is None else min(brute,val)
        assert solve(3,t)==brute
        tests.append({'t':t,'small_feasible_profiles':cnt,'oracle':'PASS'})
    rows=[]
    for t in [(0,0,0),(1,0,0),(0,1,0),(0,0,1)]:
        low=solve(92,t)
        assert 12*low>=23*SCALE
        rows.append({'t':t,'integer_lower_bound':low,'scale':SCALE,'bound':str(F(low,SCALE)),'margin_over_23_12':str(F(low,SCALE)-F(23,12))})
    print(json.dumps({'result':'PASS','domain':'all six counts 0..92; t<=1','rows':rows,'self_tests':tests},indent=2))
if __name__=='__main__':main()
