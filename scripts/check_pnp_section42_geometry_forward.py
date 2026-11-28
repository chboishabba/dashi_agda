#!/usr/bin/env python3
"""Section 42: dense polar recovery, overlap refusal, sparse exact ANF degree, PHP controls."""
import argparse, itertools, json, random, time
from collections import defaultdict
from pathlib import Path

def basis(rows):
    p={}
    for x in rows:
        x=int(x)
        while x:
            b=(x&-x).bit_length()-1
            if b in p: x^=p[b]
            else: p[b]=x; break
    return tuple(p[k] for k in sorted(p))

def nullspace(rows,n):
    p={}
    for x in rows:
        while x:
            b=(x&-x).bit_length()-1
            if b in p: x^=p[b]
            else: p[b]=x; break
    out=[]
    for f in (j for j in range(n) if j not in p):
        v=1<<f
        for b in sorted(p,reverse=True):
            if (p[b]&v).bit_count()&1: v|=1<<b
        out.append(v)
    return tuple(out)

def inter(U,V,n):
    eq=[]
    for c in range(n):
        r=sum(((u>>c)&1)<<i for i,u in enumerate(U))
        r|=sum(((v>>c)&1)<<(len(U)+i) for i,v in enumerate(V))
        if r: eq.append(r)
    vectors=[]
    for z in nullspace(eq,len(U)+len(V)):
        x=0
        for i,u in enumerate(U):
            if (z>>i)&1: x^=u
        if x: vectors.append(x)
    return basis(vectors)

def rank(rows): return len(basis(rows))
def equal(U,V): return rank(tuple(U)+tuple(V))==rank(U)==rank(V)
def transpose(A,n):
    return tuple(sum(((A[i]>>j)&1)<<i for i in range(n)) for j in range(n))
def mm(A,B,n):
    out=[]
    for row in A:
        z=0
        while row:
            b=row&-row; z^=B[b.bit_length()-1]; row^=b
        out.append(z)
    return tuple(out)
def bt_apply(B,x,n):
    return sum(((x&c).bit_count()&1)<<j for j,c in enumerate(transpose(B,n)))
def invertible(n,rng):
    attempts=0
    while True:
        attempts+=1; B=tuple(rng.getrandbits(n) for _ in range(n))
        if rank(B)==n: return B,attempts
def polar(planes,n):
    rows=[0]*n
    for u,v in planes:
        for i in range(n):
            if (u>>i)&1: rows[i]^=v
            if (v>>i)&1: rows[i]^=u
    return tuple(rows)
def cycle(n):
    if n<8 or n%2: raise ValueError("n must be even and >=8")
    U={i:[] for i in range(n//2)}; E={}; edges=[]
    for i in range(n//2):
        j=(i+1)%(n//2); P=(1<<(2*i),1<<(2*i+1))
        U[i]+=P; U[j]+=P; E[(i,j)]=basis(P); edges.append((i,j,P))
    return {i:basis(x) for i,x in U.items()},E,edges
def dense_campaign():
    out=[]
    for n in (36,48,72,96):
        U,E,edges=cycle(n); assert rank([x for _,_,P in edges for x in P])==n
        rng=random.Random(4200+n*17); B,draws=invertible(n,rng); Bt=transpose(B,n)
        recovered={}
        for v in U:
            Ps=[P for a,b,P in edges if v in (a,b)]
            recovered[v]=basis(mm(mm(Bt,polar(Ps,n),n),B,n))
        expected={k:basis(bt_apply(B,x,n) for x in P) for k,P in E.items()}
        for i in sorted(U):
            for j in range(i+1,len(U)):
                actual=inter(recovered[i],recovered[j],n)
                want=expected.get((i,j),expected.get((j,i),()))
                assert equal(actual,want),(n,i,j,len(actual),len(want))
        density=sum(x.bit_count() for x in B)/(n*n)
        assert density>.35
        out.append({"n":n,"density":round(density,6),"invertible_draws":draws,"all_intersections":True,"actual_congruence":True})
    return out
def overlap_control():
    E=[(1,2),(2,4),(4,1)]
    U=[basis(E[0]+E[2]),basis(E[0]+E[1]),basis(E[1]+E[2])]
    dims=[len(inter(U[i],U[(i+1)%3],3)) for i in range(3)]
    assert rank([x for P in E for x in P])==3 and dims==[3,3,3]
    return {"status":"OVERLAP_LATTICE_REQUIRED","summand_dimension":6,"rank":3,"pair_intersection_dimensions":dims,"claimed_edge_dimension":2}
def anf(terms):
    out=set()
    for mask in terms:
        if mask in out: out.remove(mask)
        else: out.add(mask)
    return frozenset(out)
def polar_anf(poly,n):
    rows=[0]*n
    for m in poly:
        if m.bit_count()==2:
            i=(m&-m).bit_length()-1; j=(m^(1<<i)).bit_length()-1
            rows[i]^=1<<j; rows[j]^=1<<i
    return tuple(rows)
def affine_control():
    q=anf([3,6,1,0]); q2=anf([3,6,4])
    assert polar_anf(q,3)==polar_anf(q2,3) and anf([1,1])==frozenset()
    return {"same_polar_different_affine":True,"x_squared_equals_x":True}
class SparseBasis:
    def __init__(self): self.p={}; self.rows=[]; self.work=0
    @staticmethod
    def key(m): return (m.bit_count(),m)
    def add(self,row):
        r=set(row)
        for p in sorted(self.p,key=self.key,reverse=True):
            self.work+=1
            if p in r: r.symmetric_difference_update(self.p[p])
        if not r: return False
        p=max(r,key=self.key)
        for q,s in list(self.p.items()):
            if p in s: self.p[q]=frozenset(set(s)^r)
        self.p[p]=frozenset(r); self.rows=[self.p[k] for k in sorted(self.p,key=self.key,reverse=True)]
        return True
    def contains(self,row):
        r=set(row)
        for p in sorted(self.p,key=self.key,reverse=True):
            if p in r: r.symmetric_difference_update(self.p[p])
        return not r
def clause_anf(clause):
    c=tuple(clause)
    if any(-x in c for x in c): return frozenset()
    poly=frozenset({0})
    for lit in sorted(set(c),key=lambda x:(abs(x),x)):
        b=1<<(abs(lit)-1); f=frozenset({b}) if lit<0 else frozenset({0,b})
        nxt=set()
        for x,y in itertools.product(poly,f):
            z=x|y
            if z in nxt: nxt.remove(z)
            else: nxt.add(z)
        poly=frozenset(nxt)
    return poly
def mulx(poly,j):
    out=set(); b=1<<j
    for m in poly:
        z=m|b
        if z in out: out.remove(z)
        else: out.add(z)
    return frozenset(out)
def kernel(rows,j,D):
    piv={}; rel=[]
    for i,row in enumerate(rows):
        r={m for m in row if m.bit_count()==D and not ((m>>j)&1)}; c=1<<i
        for p in sorted(piv,key=SparseBasis.key,reverse=True):
            if p in r:
                old,oc=piv[p]; r.symmetric_difference_update(old); c^=oc
        if not r: rel.append(c)
        else: piv[max(r,key=SparseBasis.key)]=(frozenset(r),c)
    return rel
def saturate(axioms,n,D,max_rows=200000,max_work=5000000,seconds=30):
    t=time.monotonic(); S=SparseBasis(); excluded=0; scans=0
    for f in axioms:
        if max((m.bit_count() for m in f),default=0)>D: excluded+=1; continue
        S.add(f)
        if S.contains({0}): return {"status":"REFUTED","degree":D,"rank":len(S.rows),"excluded_axioms":excluded}
    passes=adds=rels=0
    while True:
        passes+=1; snap=list(S.rows); changed=False
        for j in range(n):
            K=kernel(snap,j,D); rels+=len(K); scans+=sum(map(len,snap))
            for c in K:
                f=set(); bits=c
                while bits:
                    b=bits&-bits; f.symmetric_difference_update(snap[b.bit_length()-1]); bits^=b
                if S.add(mulx(f,j)):
                    adds+=1; changed=True
                    if S.contains({0}): return {"status":"REFUTED","degree":D,"rank":len(S.rows),"passes":passes,"additions":adds,"relations":rels,"logical_work_units":S.work+scans,"excluded_axioms":excluded}
            elapsed=time.monotonic()-t
            if len(S.rows)>max_rows or S.work+scans>max_work or elapsed>seconds:
                return {"status":"UNKNOWN_RESOURCE_CENSORED","degree":D,"rank":len(S.rows),"passes":passes,"additions":adds,"relations":rels,"logical_work_units":S.work+scans,"seconds":elapsed,"excluded_axioms":excluded}
        if not changed:
            return {"status":"STABLE_NO_REFUTATION","degree":D,"rank":len(S.rows),"columns_touched":len({m for r in S.rows for m in r}),"passes":passes,"additions":adds,"relations":rels,"logical_work_units":S.work+scans,"seconds":time.monotonic()-t,"excluded_axioms":excluded}
def norm_axioms(raw,n):
    out=[]
    for poly in raw:
        p=anf([int(x) for x in poly])
        if any(m<0 or m>>n for m in p): raise ValueError("monomial outside n")
        out.append(p)
    return out
def degree_case(case,limits):
    n=int(case["n"])
    if "axioms" in case: A=norm_axioms(case["axioms"],n); kind="grouped-ANF Boolean quotient"
    else: A=[clause_anf(c) for c in case["clauses"]]; kind="CNF clause-violation ANF Boolean quotient"
    ds=tuple(case.get("degrees",(0,1,2,3,4,5))); R=[saturate(A,n,d,**limits) for d in ds]
    minimum=None
    for i,r in enumerate(R):
        if r["status"]=="REFUTED":
            if all(x["status"]=="STABLE_NO_REFUTATION" for x in R[:i]): minimum=ds[i]
            break
        if r["status"]!="STABLE_NO_REFUTATION": break
    return {"source_id":case.get("source_id","unnamed"),"family":case.get("family","unlabelled"),"n":n,"proof_system":kind,"coupled_constraint_control":bool(case.get("coupled_constraint_control",False)),"results":R,"exact_minimum_in_tested_degrees":minimum}
def recovery_audit(records):
    by=defaultdict(list); out=[]
    for r in records:
        for k in ("source_id","family","n","attempts"):
            if k not in r: raise ValueError("recovery record missing "+k)
        if int(r["n"])<1 or int(r["attempts"])<0: raise ValueError("bad attempt record")
        fp=r.get("source_fingerprint")
        if fp is None and "clauses" in r: fp=repr(tuple(sorted(tuple(c) for c in r["clauses"])))
        if fp is not None: by[str(fp)].append(r)
        out.append({k:r[k] for k in ("source_id","family","n","attempts")}|{"coupled_constraint_control":bool(r.get("coupled_constraint_control",False))})
    dup=[]
    for g in by.values():
        if len({x["source_id"] for x in g})>1 and len({x["family"] for x in g})>1:
            if not all(x.get("coupled_constraint_control",False) for x in g): raise ValueError("duplicate-looking families need coupled control")
            dup.append({"source_ids":sorted(x["source_id"] for x in g),"coupled_control":True})
    out.sort(key=lambda x:(x["n"],x["source_id"]))
    by_n=defaultdict(list)
    for row in out: by_n[row["n"]].append(row["attempts"])
    trend={str(n):{"count":len(v),"min":min(v),"max":max(v),"mean":sum(v)/len(v)} for n,v in sorted(by_n.items())}
    return {"records":out,"duplicate_controls":dup,"attempts_by_n":trend,"trend":"DESCRIPTIVE_ONLY" if len(out)>1 else "INSUFFICIENT_RECORDS"}
def aux_php_source(p,h,r):
    return {"p":p,"h":h,"r":r,
      "rows":[[("x",i,j) for j in range(h)] for i in range(p)],
      "columns":[(("not",("x",i,j)),("not",("x",k,j))) for j in range(h) for i,k in itertools.combinations(range(p),2)],
      "exclude":[(("not",("e",j)),("not",("x",i,j))) for j in range(h) for i in range(p)],
      "exactly":[("e",j) for j in range(h)]}
def discover_aux_php(s):
    p,h,r=s["p"],s["h"],s["r"]
    assert len(s["rows"])==p
    row_ids=[]
    for row in s["rows"]:
        assert len(row)==h and all(t[0]=="x" for t in row)
        ids={t[1] for t in row}; holes={t[2] for t in row}
        assert len(ids)==1 and holes==set(range(h))
        row_ids.append(next(iter(ids)))
    assert set(row_ids)==set(range(p))
    pairs=set()
    for cl in s["columns"]:
        assert len(cl)==2 and all(t[0]=="not" for t in cl)
        a,b=cl[0][1],cl[1][1]
        assert a[0]==b[0]=="x" and a[2]==b[2] and a[1]!=b[1]
        pairs.add((a[2],min(a[1],b[1]),max(a[1],b[1])))
    assert pairs=={(j,a,b) for j in range(h) for a,b in itertools.combinations(range(p),2)}
    exclusions=set()
    for cl in s["exclude"]:
        assert len(cl)==2 and all(t[0]=="not" for t in cl)
        a,b=cl[0][1],cl[1][1]
        e=a if a[0]=="e" else b if b[0]=="e" else None
        x=a if a[0]=="x" else b if b[0]=="x" else None
        assert e is not None and x is not None and e[1]==x[2]
        exclusions.add((e[1],x[1]))
    assert exclusions=={(j,i) for j in range(h) for i in range(p)}
    assert set(s["exactly"])=={("e",j) for j in range(h)} and 0<=r<=h
    return {"pigeons":p,"holes":h,"excluded":r,"discovered":True}
def php_bound(p,h,r): return {"lower":p,"upper":h-r,"contradiction":p>h-r}
def clique_colour_control():
    def has_clique(n,E,k):
        return any(all(tuple(sorted((u,v))) in E for u,v in itertools.combinations(S,2)) for S in itertools.combinations(range(n),k))
    def colourable(n,E,c):
        adj=[set() for _ in range(n)]
        for u,v in E: adj[u].add(v); adj[v].add(u)
        order=sorted(range(n),key=lambda v:len(adj[v]),reverse=True); col=[-1]*n
        def go(i):
            if i==n: return True
            v=order[i]; used={col[w] for w in adj[v] if col[w]>=0}
            for x in range(c):
                if x not in used:
                    col[v]=x
                    if go(i+1): return True
                    col[v]=-1
            return False
        return go(0)
    K3=set(itertools.combinations(range(3),2))
    K22={(0,2),(0,3),(1,2),(1,3)}
    assert has_clique(3,K3,3) and not colourable(3,K3,2)
    assert colourable(4,K22,2) and not has_clique(4,K22,3)
    pairs=list(itertools.combinations(range(4),2))
    for mask in range(64):
        E={pairs[i] for i in range(6) if (mask>>i)&1}
        assert not (has_clique(4,E,3) and colourable(4,E,2))
    return {"positive_clique_side":True,"negative_colourable_side":True,"four_vertex_graphs_checked":64,
            "boundary":"semantic interpolation control only; not a Pudlak lower-bound proof"}

def selftest():
    dense=dense_campaign(); overlap=overlap_control(); affine=affine_control()
    all8=[tuple((i+1)*(1 if (a>>i)&1 else -1) for i in range(3)) for a in range(8)]
    A=[clause_anf(c) for c in all8]
    degree3=saturate(A,3,3); assert degree3["status"]=="REFUTED"
    floor=[saturate(A,3,d) for d in (0,1,2,3)]
    assert [x["status"] for x in floor]==["STABLE_NO_REFUTATION"]*3+["REFUTED"]
    scale={str(n):saturate(A,n,3) for n in (32,48)}
    assert all(x["status"]=="REFUTED" for x in scale.values())
    sat=saturate([clause_anf((1,2,3))],3,3); assert sat["status"]=="STABLE_NO_REFUTATION"
    php=discover_aux_php(aux_php_source(3,3,1)); assert php_bound(3,3,1)["contradiction"] and not php_bound(2,3,1)["contradiction"]
    grouped=degree_case({"source_id":"grouped-anf-smoke","family":"smoke-only","n":3,"degrees":[0,1,2,3],"axioms":[list(f) for f in A]}, {"max_rows":10000,"max_work":1000000,"seconds":5})
    assert grouped["proof_system"]=="grouped-ANF Boolean quotient" and grouped["exact_minimum_in_tested_degrees"]==3
    dup=recovery_audit([{"source_id":"synthetic-a","family":"hidden","n":1,"attempts":1,"source_fingerprint":"same","coupled_constraint_control":True},{"source_id":"synthetic-b","family":"hidden_extra","n":1,"attempts":2,"source_fingerprint":"same","coupled_constraint_control":True}])
    refused=False
    try:
        recovery_audit([{"source_id":"synthetic-a","family":"hidden","n":1,"attempts":1,"source_fingerprint":"same"},{"source_id":"synthetic-b","family":"hidden_extra","n":1,"attempts":2,"source_fingerprint":"same"}])
    except ValueError: refused=True
    assert refused
    clique=clique_colour_control()
    return {"status":"PASS","dense_B":dense,"overlap":overlap,"affine":affine,"degree_floor":floor,"sparse_n32_n48":scale,"satisfiable_control":sat,"grouped_anf_input_path":{"proof_system":grouped["proof_system"],"exact_minimum":grouped["exact_minimum_in_tested_degrees"]},"aux_PHP":php,"clique_colour":clique,"duplicate_attempt_audit":dup,"duplicate_guard_refuses_unlabelled":refused,"claim_ceiling":"finite controls only; no universal SAT producer or P-vs-NP endpoint"}
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--input"); p.add_argument("--output")
    p.add_argument("--max-rows",type=int,default=200000); p.add_argument("--max-work",type=int,default=5000000); p.add_argument("--seconds",type=float,default=30)
    p.add_argument("--self-test",action="store_true"); a=p.parse_args()
    report=selftest() if a.self_test or not a.input else {}
    if a.input:
        data=json.loads(Path(a.input).read_text())
        report["degree_campaigns"]=[degree_case(c,{"max_rows":a.max_rows,"max_work":a.max_work,"seconds":a.seconds}) for c in data.get("degree_cases",[])]
        report["recovery_attempt_audit"]=recovery_audit(data.get("recovery_records",[]))
    raw=json.dumps(report,indent=2,sort_keys=True)
    if a.output: Path(a.output).write_text(raw+"\n")
    print(raw)
if __name__=="__main__": main()
