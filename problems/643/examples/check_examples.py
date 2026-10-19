"""Check explicit triples using literal definitions and exact rational arithmetic."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse,hashlib,json,sys

def require(value,message):
    if not value:raise ValueError(message)

def edge(*vertices):return frozenset(vertices)

class Host:
    def __init__(self,data):
        self.vertices=data['vertices'];require(len(set(self.vertices))==len(self.vertices),'duplicate vertex')
        self.edges={frozenset(t) for t in data['edges']}
        require(len(self.edges)==len(data['edges']),'duplicate triple')
        require(all(len(t)==3 and t<=set(self.vertices) for t in self.edges),'invalid triple')
        self.pair_links=defaultdict(set);self.vertex_links=defaultdict(set)
        for t in self.edges:
            for v in t:
                p=t-{v};self.pair_links[p].add(v);self.vertex_links[v].add(p)
        self.common={edge(x,y):self.vertex_links[x]&self.vertex_links[y] for x,y in combinations(self.vertices,2)}
    def avoidance(self):
        # A repeated union of two different disjoint edge pairs gives four distinct edges:
        # if one edge were shared, its complement in the union would also be shared.
        seen={};disjoint=0
        for a,b in combinations(sorted(self.edges,key=lambda e:tuple(sorted(e))),2):
            if a.isdisjoint(b):
                disjoint+=1;union=a|b
                if union in seen:return False,False,disjoint
                seen[union]=(a,b)
        cn_ok=all(not a.isdisjoint(b) for cn in self.common.values() for a,b in combinations(cn,2))
        return True,cn_ok,disjoint
    def sigma(self,t):return sum((Q(1,len(self.pair_links[t-{v}])) for v in t),Q())
    def tau(self,t):
        return sum((Q(1,2*len(self.common[edge(v,z)])) for v in t for z in self.pair_links[t-{v}] if z!=v),Q())
    def charge(self,t):return self.sigma(t)+self.tau(t)-2
    def summary(self):
        direct,common,disjoint=self.avoidance();shadow=len(self.pair_links);colink=sum(bool(cn) for cn in self.common.values());n=len(self.vertices);e=len(self.edges)
        charges={t:self.charge(t) for t in self.edges};phi=2*e-shadow-colink
        require(sum(charges.values(),Q())==-phi,'charge-sum identity')
        return {'vertices':n,'triples':e,'shadow_pairs':shadow,'colink_pairs':colink,'binomial_n_2':n*(n-1)//2,'Phi':phi,'avoids_by_literal_disjoint_pair_unions':direct,'avoids_by_common_link_intersection':common,'disjoint_edge_pairs_checked':disjoint,'shadow_colink_equality':2*e==shadow+colink,'edge_binomial_equality':e==n*(n-1)//2,'charge_values':sorted({str(q) for q in charges.values()})}
    def bicones(self):
        out={}
        for q,cn in self.common.items():
            if len(cn)==3 and len(set().union(*cn))==3:
                members={p|{v} for p in cn for v in q};require(members<=self.edges,'bicone member missing');out[q]=(frozenset().union(*cn),members)
        return out

def local_da2(h):
    x,u,w,v,y='c','b','w','a','t';anchor=edge(x,u,w);t1=edge(x,u,v);t2=edge(x,v,w)
    ga=h.pair_links[edge(u,w)]-{x};gb=h.pair_links[edge(x,w)]-{u};gc=h.pair_links[edge(x,u)]-{w}
    def neighbors(z,group,apex):return {a for a in group if a!=z and edge(apex,z,a) in h.edges}
    da={z:(neighbors(z,gc,u),neighbors(z,gb,w)) for z in ga}
    db={z:(neighbors(z,ga,w),neighbors(z,gc,x)) for z in gb}
    dc={z:(neighbors(z,gb,x),neighbors(z,ga,u)) for z in gc}
    def cost(degrees):return Q(1,2*(1+sum(map(len,degrees))))
    au={z for z,(ru,rw) in da.items() if ru and not rw};aw={z for z,(ru,rw) in da.items() if rw and not ru}
    rx={z for z,(rx,ru) in dc.items() if rx and not ru};r2={z for z,(rx,ru) in dc.items() if rx and ru}
    rpx={z for z,(rw,rx) in db.items() if rx and not rw};rp2={z for z,(rw,rx) in db.items() if rx and rw};rp0={z for z,d in db.items() if not any(d)}
    wm=Q(1,len(h.pair_links[edge(x,w)]))+sum((cost(db[z]) for z,d in db.items() if not all(d)),Q())+sum((cost(da[z]) for z in aw),Q())-sum((cost(db[z]) for z in rpx|rp0),Q())
    xcost=sum((cost(dc[z]) for z in rx),Q())+sum((cost(db[z]) for z in rpx),Q())+Q(len(r2)+len(rp2),6)
    hw=wm+Q(len(rp0),2)-Q(11,12)+xcost
    m,mp=len(r2),len(rp2)
    tauw=Q(int(mp==1),12) if m==0 else Q(1,6) if m==mp==1 else Q(1,12) if m==1 else Q(m,3*(m+3))+Q(int(mp==1),12)
    charges={t:h.charge(t) for t in h.edges};bic=h.bicones();active={q for q,(base,members) in bic.items() if any(charges[t]<0 for t in members)}
    containing={q for q in active if anchor in bic[q][1]};base,members=bic[edge(x,y)];deficient={t for t in members if x in t and charges[t]<0};deficit=sum((-charges[t] for t in deficient),Q());act=len(containing);kuw=len(h.pair_links[edge(u,w)])
    require(base==edge('a','b','w') and deficient=={t1},'DA2 bicone/deficiency changed')
    require(containing=={edge('c','t'),edge('w','r')},'DA2 active anchor bicones changed')
    coordinates=[len(rpx),len(rx),len(r2),len(rp2)]
    expected={'coordinates':[1,0,1,0],'charge_T1':'-409/755160','charge_T2':'1/2','charge_anchor':'367/1566','deficit_at_apex':'409/755160','anchor_margin':'792709/6796440','strict_claim_margin':'675529/3398220','W_minus':'7/12','X_cost':'5/12','H_w':'1/12','tau_W':'1/12'}
    out={'coordinates':coordinates,'coordinate_order':['n_B','n_C','m','m_prime'],'charge_T1':str(charges[t1]),'charge_T2':str(charges[t2]),'charge_anchor':str(charges[anchor]),'deficit_at_apex':str(deficit),'active_anchor_bicones':[sorted(q) for q in sorted(containing,key=lambda q:tuple(sorted(q)))],'act_anchor':act,'k_uw':kuw,'anchor_margin':str(charges[anchor]/act-deficit),'strict_claim_margin':str(charges[anchor]-act*deficit-Q(1,kuw)),'W_minus':str(wm),'X_cost':str(xcost),'H_w':str(hw),'tau_W':str(tauw),'groups':{'A':sorted(ga),'B':sorted(gb),'C':sorted(gc)},'B_relation_degrees':{z:list(map(len,d)) for z,d in sorted(db.items())},'C_relation_degrees':{z:list(map(len,d)) for z,d in sorted(dc.items())}}
    for key,value in expected.items():require(out[key]==value,'DA2 local value changed: '+key)
    require(act==2 and kuw==29,'DA2 denominator changed')
    return out

def controls():
    bad=Host({'vertices':list('abcdef'),'edges':[list(s) for s in ['abc','def','abd','cef']]})
    direct,common,_=bad.avoidance();require(not direct,'literal forbidden configuration accepted')
    # Compute CN rejection independently even though literal avoidance returns early.
    require(any(a.isdisjoint(b) for cn in bad.common.values() for a,b in combinations(cn,2)),'common-link forbidden configuration accepted')
    small=Host({'vertices':list('abcde'),'edges':[[*p,x] for p in combinations('abc',2) for x in 'de']})
    require(small.summary()['Phi']==-1,'non-equality cone control accepted')
    return {'literal_forbidden_configuration_rejected':True,'disjoint_common_link_pairs_rejected':True,'cone2_not_misclassified_as_shadow_colink_equality':True}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--data',type=Path,default=Path(__file__).resolve().parent/'hosts');args=parser.parse_args()
    results={'scope':'Three explicit finite hosts; not universal theorem verification','negative_controls':controls(),'hosts':{}}
    for name in ['da2','cone3','cone4']:
        path=args.data/(name+'-host.json');data=json.loads(path.read_text());h=Host(data);summary=h.summary();require(summary['avoids_by_literal_disjoint_pair_unions'] and summary['avoids_by_common_link_intersection'],'host is not avoiding')
        if name=='da2':require(summary['vertices']==78 and summary['triples']==1307,'DA2 host size changed');summary['local']=local_da2(h)
        else:
            k=int(name[-1]);require(summary['triples']==3*k and summary['shadow_pairs']==3+3*k and summary['colink_pairs']==3+k*(k-1)//2,'cone counts changed');require(summary['Phi']==0 and summary['charge_values']==['0'],'cone charge equality changed');require(summary['shadow_colink_equality'] and not summary['edge_binomial_equality'],'two equalities conflated')
            for t in h.edges:require(h.sigma(t)==1+Q(1,k) and h.tau(t)==Q(1,k)+Q(k-1,6),'cone local formula changed')
            summary['sigma_each']=str(1+Q(1,k));summary['tau_each']=str(Q(1,k)+Q(k-1,6))
        summary['input_sha256']=hashlib.sha256(path.read_bytes()).hexdigest();results['hosts'][name]=summary
    results['result']='PASS';print(json.dumps(results,indent=2,sort_keys=True))

if __name__=='__main__':main()
