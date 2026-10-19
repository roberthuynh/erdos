from fractions import Fraction as F
from itertools import product
import json
rows=[]
for b,c,m,h in product(range(12),range(12),range(7),range(7)):
    if not 1<=m+h<=6:continue
    for mutual in ([False,True] if m==h==1 else [False]):
        if not b+h or not c+m:continue
        if mutual:
            if (b==0)!=(c==0):continue
            rx=F(b,2*(c+1))+F(c,2*(b+1));target=F(1,12)
        else:
            if (m and not b) or (h and not c):continue
            if not c and b>int(m>0):continue
            if not b and c>int(h>0):continue
            rx=F(b-int(m>0),2*(c+1))+F(c-int(h>0),2*(b+1))
            if m:rx+=F(1,2*(c+m+1))
            if h:rx+=F(1,2*(b+h+1))
            target=F(int(h==1),12) if m==0 else F(1+int(h==1),12) if m==1 else F(m,3*(m+3))+F(int(h==1),12)
        beta=F(1,4)+F(1,b+h+2) if not h else F(1,6)+F(1,b+h+2)+F(1,2*(h+2))
        gap=beta+rx+F(m+h,6)-F(11,12)-target
        assert gap>=0,(b,c,m,h,mutual,gap)
        rows.append((gap,(b,c,m,h,mutual)))
print(json.dumps({'points':len(rows),'minimum':str(min(v for v,_ in rows)),'equality':[p for v,p in rows if v==0],'false_side_bound_at_m40_h1':str(F(40,129)+F(1,12)-F(11,28))}))
