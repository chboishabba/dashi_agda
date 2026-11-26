"""Original signed monotone exchange via deterministic count factors.

Reuse dependency decomposition and collective syndrome absorption. No pairing
multiplicity in the count representation. All receipts scoped to fixed R,P,x.
"""
from random import Random
from itertools import combinations
from check_pnp_affine_normal_components import bits, canon, chart, lift, satisfies, Budget, Exhausted
from check_pnp_normal_boundary_join import value
import check_p0_dependency_phase_20261125 as D
from check_p0_collective_image_descent_20261125 import collective


def surplus(R,x,v):
    return tuple((r&x&v).bit_count()-(r&v&~x).bit_count() for r in R)


def pairing_receipt(R,x,v):
    """Canonical original-index pairing; return None on incompatible movement."""
    out=[]
    for r in R:
        a=list(bits(r&v&~x));b=list(bits(r&v&x));d=len(b)-len(a)
        if d<0 or d%2:return None
        out.append(tuple(zip(a,b[:len(a)]))+tuple(zip(b[len(a)::2],b[len(a)+1::2])))
    return tuple(out)


def pairing_onehot(n,R,P,x,B):
    """Explicit shared-bit pairing source with homogeneous retained equations."""
    F=[];roots=[];d=n
    for r in R:
        J=list(bits(r));ports={j:[(1<<j,1)] for j in J}
        for j,k in combinations(J,2):
            B.pay('exchange_pair_edge')
            if not ((x>>j&1) or (x>>k&1)):continue
            a=1<<d;d+=1;ports[j].append((a,0));ports[k].append((a,0))
            if (x>>j&1) and (x>>k&1):roots.append((a,1))
        F.extend(tuple(ports[j]) for j in J)
    return d,tuple(F),tuple((a,0) for a,b in P),tuple(roots)


def factors(n,R,P,x,B,small=5):
    """Exact local functional supports. Each row has one terminal root factor.

    A prefix count adds v for removed columns and 1-v for added columns.
    Final count minus number of addable columns is signed surplus.
    For large rows use deterministic binary count transitions (unique extension).
    """
    assert 0<=small<=8 and P==canon(P) and satisfies(x,P,())
    assert canon(P+tuple((r,1) for r in R))==P
    B.pay('exchange_chart',1+n*(1+len(P)))
    _,V=chart(n,tuple((a,0) for a,b in P));d=len(V);blocks=[];roots=[];z0=0
    def add(N,T,Z=()):
        # Canonical local basis; discard unattainable local labels, preserve root subset.
        U=tuple(a for a,b in canon((a,0) for a in N));allopts=set();positive=set();Z=set(Z)
        for p in T:
            B.pay('exchange_local_label',1+len(N)*(1+d))
            H=canon((a,p>>i&1) for i,a in enumerate(N))
            if H is None:continue
            q=value(U,chart(d,H)[0]);allopts.add(q)
            if p in Z:positive.add(q)
        blocks.append((U,sorted(allopts)))
        return len(blocks)-1,sorted(positive)
    for e,r in enumerate(R):
        J=list(bits(r));m=len(J);N=tuple(value(V,1<<j) for j in J);a=sum(not (x>>j&1) for j in J)
        B.pay('exchange_row',1+m*(1+len(V)))
        U=tuple(a for a,b in canon((a,0) for a in N))
        if len(U)<=small:
            pos=[];ok=[]
            for p in range(1<<len(U)):
                B.pay('exchange_small_pattern',1+m+len(U))
                y=chart(len(V),tuple((a,p>>i&1) for i,a in enumerate(U)))[0]
                s=sum((1 if x>>j&1 else -1)*((a&y).bit_count()%2) for j,a in zip(J,N))
                if s>=0 and s%2==0:ok.append(p)
                if s>0 and s%2==0:pos.append(p)
            roots.append((len(blocks),pos));blocks.append((U,ok));continue
        prev=();width=m.bit_length();count=0
        for i,j in enumerate(J):
            cur=tuple(1<<(d+k) for k in range(width))
            count+=int(not (x>>j&1));z0|=count<<d;d+=width
            T=[];k=len(prev)
            for s in range(i+1):
                for b in (0,1):
                    B.pay('exchange_count_transition')
                    t=s+(b if x>>j&1 else 1-b)
                    T.append(s|(b<<k)|(t<<(k+1)))
            add(prev+(N[i],)+cur,T);prev=cur
        roots.append(add(prev,range(a,m+1,2),range(a+2,m+1,2)))
    return d,V,blocks,roots,z0


class ProbeExhausted(Exception): pass


class ProbeBudget:
    """Local ceiling, shared parent charge; no resetting global work."""
    def __init__(self,B,cap):self.B=B;self.left=cap;self.stats=B.stats
    def pay(self,tag,n=1):
        if n>self.left:raise ProbeExhausted
        self.B.pay(tag,n);self.left-=n


def rado_root(d,blocks,B):
    """Reuse existing forbidden-flat transversal and boundary solver."""
    from check_pnp_affine_normal_components import simplify
    from check_pnp_normal_transversal import transversal, reopen_core
    from check_pnp_normal_boundary_join import join
    F=[]
    for U,T in blocks:
        allowed=set(T)
        # Explicit local support complement; charge BEFORE expansion.
        B.pay('exchange_rado_flat',(1+len(U))*(1<<len(U)))
        F.extend(tuple((a,p>>i&1) for i,a in enumerate(U)) for p in range(1<<len(U)) if p not in allowed)
    H=simplify(tuple(F),B)
    if () in H:return 'UNSAT',None
    chosen,R=transversal(H,B);B.pay('exchange_rado_core',1+len(H))
    z,_=join(d,tuple(H[j] for j in R),B)
    if z is None:return 'UNSAT',None
    B.pay('exchange_rado_reopen',1+d*(1+len(H)))
    z=reopen_core(d,H,chosen,R,z)
    return 'SAT',[value(U,z) for U,T in blocks]


def discover(n,R,P,x,B,rank_cap=8,probe_cap=1000000,small=5,rado=False,tagged=False):
    """Return (movement, decisive). Decisive None excludes every positive root.

    The bounded producer does not promise success on every inhabited source.
    Each root changes one local factor. Unchanged dependency components have
    the canonical zero-movement extension, so only its own component is solved.
    """
    assert 0<=rank_cap<=16 and probe_cap>=0
    d,V,blocks,roots,z0=factors(n,R,P,x,B,small)
    L=sum(len(U) for U,T in blocks)
    B.pay('exchange_dependency',1+len(blocks)+L*(1+L));ranges,comps,_=D.decompose(blocks)
    owners={i:(ids,rels) for ids,rels in comps for i in ids}
    # A zero-movement assignment determines all auxiliary counts. Instead of
    # reconstructing those bits, use the fact its local labels exist, and reopen
    # only the original movement normals belonging to the solved component.
    # All components' local normal spans are independent (dependency components).
    # Root-local exclusions can be reused globally on this fixed carrier:
    # no positive surplus at row e means every feasible trade has zero there.
    versions={ids[0]:0 for ids,rels in comps};pending=set(range(len(roots)));seen={}
    def reopen(ids,Y,Q):
        selected=dict(zip(ids,Y));rows=[]
        Q.pay('exchange_reopen',1+d*(1+L)+sum(len(S) for U,S in blocks))
        for j,(U,S) in enumerate(blocks):
            p=selected[j] if j in selected else value(U,z0);assert p in S
            rows.extend((a,p>>k&1) for k,a in enumerate(U))
        z=D.lift(rows);assert z is not None;v=lift(0,V,z&((1<<len(V))-1))
        Q.pay('exchange_verify',1+n+sum(r.bit_count() for r in R))
        q=surplus(R,x,v);assert all(a>=0 and a%2==0 for a in q) and any(q)
        assert satisfies(x^v,P,()) and pairing_receipt(R,x,v) is not None
        return v,q
    if tagged:
        # A positive local label may emit one optional tag. An odd XOR of
        # tags proves at least one positive row; no root loop needed if exact.
        # Tags are auxiliary witness choices, never counted as original trades.
        positive={i:set(T) for i,T in roots}
        for ids,rels in comps:
            E=[e for e,(i,T) in enumerate(roots) if i in ids and T]
            if not E:continue
            Q=ProbeBudget(B,probe_cap);B.pay('exchange_tag_probe')
            try:
                Q.pay('exchange_tag_choices',1+sum(len(blocks[j][1])*(1+len(blocks[j][0]))*(1+len(rels)) for j in ids))
                C=D.choices(blocks,ranges,ids,rels);tag=1<<len(rels);M=[]
                for j,O in zip(ids,C):
                    Q.pay('exchange_tag_options',1+2*len(O))
                    A=[(p<<1,t) for p,t in O]
                    A.extend(((p<<1)|1,t^tag) for p,t in O if p in positive.get(j,()))
                    M.append(A)
                status,Y,_=collective(M+[[(0,tag)]],len(rels)+1,rank_cap,B=Q)
                if status=='SAT':
                    assert any(p&1 for p in Y[:-1]);v,q=reopen(ids,[p>>1 for p in Y[:-1]],Q)
                    B.pay('exchange_tag_witness');return v,True
                if status=='UNSAT':
                    for e in E:pending.remove(e)
                    B.pay('exchange_tag_empty',len(E))
                else:B.pay('exchange_tag_unknown')
            except ProbeExhausted:B.pay('exchange_tag_unknown')
    while pending:
        e=next((e for e in sorted(pending) if seen.get(e,-1)!=versions[owners[roots[e][0]][0][0]]),None)
        B.pay('exchange_schedule',1+len(pending))
        if e is None:break
        i,T=roots[e];ids,rels=owners[i];key=ids[0]
        if e in seen:B.pay('exchange_retry')
        seen[e]=versions[key]
        B.pay('exchange_root')
        if not T:
            pending.remove(e);B.pay('exchange_root_empty');continue
        Q=ProbeBudget(B,probe_cap)
        try:
            Q.pay('exchange_root_factors',1+len(blocks))
            local=[(U,T if j==i else S) for j,(U,S) in enumerate(blocks)]
            Q.pay('exchange_choices',1+sum(len(local[j][1])*(1+len(local[j][0]))*(1+len(rels)) for j in ids))
            C=D.choices(local,ranges,ids,rels)
            status,Y,st=collective(C,len(rels),rank_cap,B=Q)
            if status=='UNKNOWN' and rado:
                status,Y=rado_root(d,[local[j] for j in ids],Q)
            if status=='UNKNOWN':B.pay('exchange_root_unknown');continue
            if status=='UNSAT':
                U,S=blocks[i];bad=set(T);B.pay('exchange_learn',1+len(S)+len(T))
                T0=[p for p in S if p not in bad];assert len(T0)<len(S) and value(U,z0) in T0
                blocks[i]=(U,T0);versions[key]+=1;pending.remove(e)
                B.pay('exchange_root_empty');continue
            v,q=reopen(ids,Y,Q);assert q[e]>0
            B.pay('exchange_root_witness');return v,True
        except ProbeExhausted:
            B.pay('exchange_root_unknown')
    return None,not pending



def descent(n,R,P,x,B,rank_cap=8,probe_cap=1000000,small=5,rado=False,tagged=False,history=None,k_index=0):
    """Monotone source descent. UNKNOWN never proves no cover."""
    k=len(R)//3;t=0
    assert len(R)%3==0 and all(sum((r>>j)&1 for r in R)==3 for j in range(n))
    while x.bit_count()>k:
        B.pay('exchange_descent')
        # Cheap exact removal-only bypass in the retained homogeneous space.
        H=canon(tuple((a,0) for a,b in P)+tuple((1<<j,0) for j in range(n) if not (x>>j&1)))
        _,V=chart(n,H);B.pay('exchange_removal_kernel',1+n*(1+len(P)))
        if V:v,done=V[0],True
        else:v,done=discover(n,R,P,x,B,rank_cap,probe_cap,small,rado,tagged)
        if v is None:return None,done
        y=x^v;q=surplus(R,x,v)
        assert all(t>=0 and t%2==0 for t in q) and any(q)
        assert satisfies(y,P,()) and y.bit_count()<=x.bit_count()-2
        if history is not None:history.append((k_index,t,x,v,q,B.left))
        x=y;t+=1
    assert all((x&r).bit_count()==1 for r in R)
    return x,True
