import check_profiles as c
import itertools,json
from fractions import Fraction as F
rows=[]
for t in [(0,0,0),(1,0,0),(2,2,2),(0,2,3)]:
    M=[x[:5,:5] for x in c.mats(t)];D=M[0]
    for mat in M[1:]:D=c.mp(D,mat)
    dp=int(c.np.diag(D).min())
    brute=c.INF; rational=None;count=0
    for x in itertools.product(range(5),repeat=6):
        val=sum(int(M[i][x[i],x[(i+1)%6]]) for i in range(6))
        brute=min(brute,val)
        if val>=c.INF:continue
        rat=c.exact(x,t);count+=1
        assert F(val,c.SCALE)+F(sum(t),6)<=rat
        rational=rat if rational is None else min(rational,rat)
    assert dp==brute
    rows.append({'t':t,'profiles':count,'integer_dp_equals_exhaustive':True,'exact_minimum':str(rational)})
print(json.dumps(rows))
