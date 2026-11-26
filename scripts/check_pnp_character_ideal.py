"""Odd-field signed character-ideal exclusion on original exact-one rows.
Classical polynomial calculus in the binary character group algebra.
Finite caps are optional proof discovery limits, not completeness claims.
"""
from itertools import combinations
from check_pnp_affine_normal_components import Budget, canon, chart, lift
from check_pnp_normal_boundary_join import value

PRIMES=(3,5,7,11,101)


def add(A,B,c,p):
    for s,w in B.items():
        v=(A.get(s,0)+c*w)%p
        if v:A[s]=v
        elif s in A:del A[s]


def generators(F,p,pairs=True,B=None):
    """2(sum bits-1), and 4 times each within-row bit product."""
    assert p in PRIMES
    for G in F:
        if B is not None:B.pay('character_source',1+len(G)+(len(G)*(len(G)-1)//2 if pairs else 0))
        A={};add(A,{0:len(G)-2},1,p)
        for s,b in G:add(A,{s:-(-1)**b},1,p)
        yield A
        if pairs:
            for (s,b),(t,c) in combinations(G,2):
                A={}
                for u,w in ((0,1),(s,-(-1)**b),(t,-(-1)**c),(s^t,(-1)**(b+c))):add(A,{u:w},1,p)
                yield A


def eliminate(F,shifts,p,B,pairs=True,max_pivots=4096):
    """Return the source proof rows and whether constant one was derived."""
    assert p in PRIMES and max_pivots>=0
    G=tuple(generators(F,p,pairs,B));basis={};proof=[]
    for t in shifts:
        for j,g in enumerate(G):
            B.pay('character_generator',1+len(g));A={s^t:w for s,w in g.items()};ops=[]
            while A:
                s=max(A);w=A[s]
                if s not in basis:break
                k,C=basis[s];B.pay('character_reduce',1+len(C));add(A,C,-w,p);ops.append((k,-w%p))
            if not A:continue
            s=max(A);c=pow(A[s],-1,p);A={u:w*c%p for u,w in A.items()}
            B.pay('character_pivot',1+len(A)+len(ops))
            if s==0:return tuple(proof+[(j,t,tuple(ops),c)]),True
            if len(basis)>=max_pivots:return tuple(proof),False
            basis[s]=(len(proof),A);proof.append((j,t,tuple(ops),c))
    return tuple(proof),False


def exclude(F,shifts,p,B,pairs=True,max_pivots=4096):
    """Return a replayable constant contradiction, or None (inconclusive)."""
    proof,empty=eliminate(F,shifts,p,B,pairs,max_pivots)
    return proof if empty else None


def replay(F,proof,p,pairs=True,B=None):
    """Replay source combinations; never trust producer pivot decisions."""
    if p not in PRIMES or proof is None:return None
    G=tuple(generators(F,p,pairs,B));rows=[]
    for j,t,ops,c in proof:
        if not (0<=j<len(G) and t>=0 and 0<c<p):return None
        if B is not None:B.pay('character_verify_source',1+len(G[j]))
        A={s^t:w for s,w in G[j].items()}
        for k,w in ops:
            if not (0<=k<len(rows) and 0<=w<p):return None
            if B is not None:B.pay('character_verify_reduce',1+len(rows[k]))
            add(A,rows[k],w,p)
        if B is not None:B.pay('character_verify_row',1+len(A))
        rows.append({s:w*c%p for s,w in A.items()})
    return rows


def verify(F,proof,p,pairs=True,B=None):
    rows=replay(F,proof,p,pairs,B)
    return bool(rows) and rows[-1]=={0:1}


def source_shifts(F,degree=1,B=None):
    if degree not in (0,1,2):raise ValueError("degree must be 0, 1 or 2")
    S=sorted({s for G in F for s,b in G if s});T={0}
    if B is not None:B.pay("character_shift_build",1+sum(map(len,F))+len(S)+(len(S)*(len(S)-1)//2 if degree==2 else 0))
    if degree>=1:T.update(S)
    if degree>=2:T.update(s^t for s,t in combinations(S,2))
    return sorted(T,key=lambda t:(t!=0,t))


def compact(proof,B=None):
    """Retain only the transitive dependencies of the final contradiction."""
    active={len(proof)-1};todo=list(active)
    while todo:
        i=todo.pop();ops=proof[i][2]
        if B is not None:B.pay('character_proof_slice',1+len(ops))
        for k,w in ops:
            if k not in active:active.add(k);todo.append(k)
    ids={i:j for j,i in enumerate(sorted(active))}
    return tuple((j,t,tuple((ids[k],w) for k,w in ops),c)
                 for i in sorted(active) for j,t,ops,c in (proof[i],))


def transport_proof(proof,V,a,p,B=None):
    """Pull the exact certificate along z=a XOR V y, with stable generator IDs."""
    if p not in PRIMES:raise ValueError("unsupported odd prime")
    out=[]
    for j,t,ops,c in proof:
        if B is not None:B.pay('character_transport',1+len(V)+len(ops))
        sign=(-1)**((t&a).bit_count()%2)
        out.append((j,value(V,t),tuple((k,w*sign%p) for k,w in ops),c*sign%p))
    return tuple(out)


def demand_exclusion(n,F,H,B,degree=1,p=3,max_pivots=4096):
    """Verify exclusion on the exact demanded affine fibre; False is UNKNOWN."""
    B.pay("character_demand",1+len(H))
    P=canon(H)
    if P is None:return True
    u,V=chart(n,P);B.pay('character_pullback',1+sum(len(G) for G in F)*(1+len(V)))
    R=tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)
    S=source_shifts(R,degree,B);B.pay('character_shifts',len(S))
    proof=exclude(R,S,p,B,max_pivots=max_pivots)
    if proof is None:return False
    if not verify(R,compact(proof,B),p,B=B):raise AssertionError('invalid character contradiction')
    return True


def quotient_normal(A,basis,p,B):
    """Reduce every pivot column, including those below free columns."""
    A=dict(A);R={}
    while A:
        s=max(A);w=A[s]
        if s in basis:
            C=basis[s];B.pay('character_normal',1+len(C));add(A,C,-w,p)
        else:
            B.pay('character_free');R[s]=A.pop(s)
    return R


def replay_span(F,proof,p,B,pairs=True):
    """Rebuild a span from replayed source combinations; rechart can merge pivots."""
    R=replay(F,proof,p,pairs,B)
    if R is None:return None
    basis={}
    for A in R:
        C=dict(A)
        while C and max(C) in basis:
            s=max(C);D=basis[s];B.pay('character_replay_pivot',1+len(D));add(C,D,-C[s],p)
        if C:
            s=max(C);c=pow(C[s],-1,p);basis[s]={t:w*c%p for t,w in C.items()}
    return basis


def character_relation_span(F,shifts,queries,p,B,max_pivots=4096):
    """Retain a replayed proof span and explicit proportionality certificates."""
    proof,empty=eliminate(F,shifts,p,B,max_pivots=max_pivots)
    if empty:proof=compact(proof,B) # preserve compact contradiction replay
    basis=replay_span(F,proof,p,B)
    if basis is None:raise AssertionError('invalid character proof')
    if empty:
        assert not quotient_normal({0:1},basis,p,B)
        return proof,(),0,basis
    groups={};relations=[]
    for s in sorted(set(queries)|{0}):
        B.pay('character_query');A=quotient_normal({s:1},basis,p,B)
        if not A:return proof,(),s,basis
        c=A[min(A)];inv=pow(c,-1,p)
        B.pay('character_projective_key',1+len(A))
        key=tuple(sorted((t,w*inv%p) for t,w in A.items()))
        if key in groups:
            t,d=groups[key];ratio=c*pow(d,-1,p)%p
            relations.append((s,t,ratio))
            if ratio not in (1,p-1):break
        else:groups[key]=(s,c)
    return proof,tuple(relations),None,basis


def character_relations(F,shifts,queries,p,B,max_pivots=4096):
    proof,relations,zero,_=character_relation_span(F,shifts,queries,p,B,max_pivots)
    return proof,relations,zero


def span_accepts_relations(basis,relations,zero,p,B):
    if zero is not None:
        return not relations and zero>=0 and not quotient_normal({zero:1},basis,p,B)
    for s,t,c in relations:
        if min(s,t)<0 or not 0<c<p:return False
        A={s:1};add(A,{t:1},-c,p)
        if quotient_normal(A,basis,p,B):return False
    return True


def verify_relations(F,proof,relations,zero,p,B):
    """Replay from original generators; verify the claimed proportionalities."""
    basis=replay_span(F,proof,p,B)
    return basis is not None and span_accepts_relations(basis,relations,zero,p,B)


def relation_pins(relations,zero,p):
    if zero is not None or any(c not in (1,p-1) for s,t,c in relations):return None
    return canon((s^t,int(c!=1)) for s,t,c in relations)


def transport_relations(relations,zero,V,a,p):
    return (tuple((value(V,s),value(V,t),c*(-1)**(((s^t)&a).bit_count()%2)%p)
                  for s,t,c in relations),None if zero is None else value(V,zero))


def character_consequences(F,shifts,probes,p,B,max_pivots=4096):
    """Verified affine consequences; None is a certified contradiction."""
    proof,relations,zero,basis=character_relation_span(F,shifts,probes,p,B,max_pivots)
    if not span_accepts_relations(basis,relations,zero,p,B):raise AssertionError('invalid character consequence')
    return relation_pins(relations,zero,p)


def quotient_reopen(n,F,basis,p,B,cap=64):
    """Attempt an original witness using a capped finite character module.

    Full ideal closure makes its multiplication maps commuting involutions.
    Partial spans need not have that property: check the eigensection and
    independently verify the original row assignment. Failure is UNKNOWN.
    """
    if cap<1 or 0 in basis:return None
    S=tuple(s for s,b in canon((s,0) for G in F for s,b in G))
    Q=[0];seen={0};M={};i=0
    while i<len(Q):
        t=Q[i];i+=1
        for s in S:
            B.pay('character_module_edge');A=quotient_normal({s^t:1},basis,p,B)
            M[s,t]=A
            for a in A:
                if a not in seen:
                    if len(Q)>=cap:return None
                    Q.append(a);seen.add(a)
    B.pay('character_module_dimension',len(Q))
    def act(s,v):
        out={}
        for t,w in v.items():
            A=M[s,t];B.pay('character_module_act',1+len(A));add(out,A,w,p)
        return out
    def eigen(s,v,b):
        A=act(s,v);add(A,v,-(-1)**b,p);return not A
    v={0:1};pins=[]
    for s in S:
        w=act(s,v);u=dict(v);add(u,w,1,p);b=0
        if not u:
            b=1;u=dict(v);add(u,w,-1,p)
        if not u or not eigen(s,u,b):return None
        pins.append((s,b));v=u
    if not all(eigen(s,v,b) for s,b in pins):return None
    P=canon(pins);assert P is not None
    x=chart(n,P)[0]
    B.pay('character_module_verify',1+sum(map(len,F)))
    if not all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F):return None
    return x


def section_project(q,s,b,basis,p,B):
    """One original signed bit projector, reduced only modulo verified rows."""
    B.pay('character_section_product',1+2*len(q))
    A=dict(q);add(A,{t^s:w for t,w in q.items()},-(-1)**b,p)
    return quotient_normal(A,basis,p,B)


def lazy_section(n,F,basis,p,B,cap=64):
    """Select a verified original one-hot section without closing a module.

    A zero reduced projector excludes its prefix on the actual solution set.
    Nonzero does not prove inhabitation for an incomplete span. All failures
    return None; the selected branch is never exported as a global pin.
    cap bounds retained section support, not all elimination intermediates.
    """
    if cap<1 or 0 in basis:return None
    q={0:1};H=()
    for G in F:
        candidates=[]
        for j,(s,b) in enumerate(G):
            B.pay('character_section_pattern',1+len(H)+len(G))
            P=canon(H+tuple((t,c^int(i==j)) for i,(t,c) in enumerate(G)))
            if P is not None:candidates.append((j,P))
        if not candidates:return None
        if len(candidates)==1:
            H=candidates[0][1];continue
        best=None
        for j,P in candidates:
            s,b=G[j];A=section_project(q,s,b,basis,p,B)
            if not A:
                B.pay('character_section_zero');continue
            if len(A)>cap:continue
            key=(len(A),-len(P),j)
            if best is None or key<best[0]:best=(key,P,A)
            if len(A)==1:break
        if best is None:return None
        _,H,q=best
        c=pow(q[min(q)],-1,p);q={s:w*c%p for s,w in q.items()}
        B.pay('character_section_retained',len(q))
    x=chart(n,H)[0]
    B.pay('character_section_verify',1+sum(map(len,F)))
    if not all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F):return None
    return x


def restrict_character_span(basis,V,a,p,B):
    """Linear image of the replayed consequence span under an affine embedding."""
    out={};freq={}
    for C in basis.values():
        A={}
        for s,w in C.items():
            if s not in freq:
                B.pay('character_restrict_map',1+len(V))
                freq[s]=(value(V,s),(-1)**((s&a).bit_count()%2))
            t,c=freq[s];B.pay('character_restrict_term');add(A,{t:w},c,p)
        while A and max(A) in out:
            s=max(A);D=out[s];B.pay('character_restrict_reduce',1+len(D));add(A,D,-A[s],p)
        if A:
            s=max(A);c=pow(A[s],-1,p);out[s]={t:w*c%p for t,w in A.items()}
            B.pay('character_restrict_pivot',1+len(A))
            if s==0:return out
    return out


def extend_character_span(F,basis,p,B,degree=1,max_pivots=256):
    """Add locally shifted original equations to an already verified span.

    All new rows are explicit linear combinations of shifted original generators
    and retained rows. A rank cap only stops discovery; it proves nothing.
    """
    assert max_pivots>=0
    out=dict(basis)
    if 0 in out:return out
    G=tuple(generators(F,p,B=B))
    for t in source_shifts(F,degree,B):
        for g in G:
            B.pay('character_local_generator',1+len(g))
            A={s^t:w for s,w in g.items()}
            A=quotient_normal(A,out,p,B)
            if not A:continue
            s=max(A)
            if s!=0 and len(out)>=max_pivots:return out
            c=pow(A[s],-1,p);out[s]={v:w*c%p for v,w in A.items()}
            B.pay('character_local_pivot',1+len(A))
            if s==0:return out
    return out


def verify_onehot_exclusion(F,e,j,certificate,p,B):
    """Replay a parent combination of shifted original generators as 2*x_ej."""
    if p not in PRIMES or not (0<=e<len(F) and 0<=j<len(F[e])):return False
    G=tuple(generators(F,p,True,B));A={}
    for k,t,c in certificate:
        if not (0<=k<len(G) and t>=0 and 0<c<p):return False
        B.pay('character_lift_replay',1+len(G[k]));add(A,{s^t:w for s,w in G[k].items()},c,p)
    s,b=F[e][j];target={0:1};add(target,{s:1},-(-1)**b,p)
    return A==target


def lift_onehot_exclusion(n,F,e,j,proof,p,B):
    """Lift a verified child constant proof to a sparse parent proof of 2*x_ej.

    The child must be the actual one-hot restriction of row e to choice j.
    A different restriction, invalid proof, or inconsistent chart is rejected.
    No exponential product of all branch indicator equations is formed.
    """
    assert p in PRIMES and 0<=e<len(F) and 0<=j<len(F[e])
    row=F[e];H=canon((s,b^int(i==j)) for i,(s,b) in enumerate(row))
    if H is None:return None
    a,V=chart(n,H);R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
    if not verify(R,proof,p,B=B):return None
    # Flatten the terminal proof DAG by reverse accumulation. Each proof row
    # contributes just one shifted generator; merge equal terms.
    coeff={len(proof)-1:1};C={};maps={};G=tuple(generators(F,p,True,B))
    for i in range(len(proof)-1,-1,-1):
        w=coeff.get(i,0)
        if not w:continue
        k,t,ops,c=proof[i];w=w*c%p;B.pay('character_lift_dag',1+len(ops))
        for h,v in ops:coeff[h]=(coeff.get(h,0)+w*v)%p
        if t not in maps:
            if t>>len(V):return None
            Q=canon((v,(t>>l)&1) for l,v in enumerate(V))
            if Q is None:return None
            B.pay('character_lift_map',1+n*len(V));maps[t]=chart(n,Q)[0]
        s=maps[t];add(C,{(k,s):w},(-1)**((s&a).bit_count()%2),p)
    f={};out={};s0,b0=row[j];eps=(-1)**b0
    for (k,s),w in C.items():
        B.pay('character_lift_expand',1+len(G[k]))
        add(f,{t^s:v for t,v in G[k].items()},w,p)
        add(out,{(k,s):w},1,p);add(out,{(k,s^s0):w},-eps,p)
    h={0:1};add(h,f,-1,p)
    # h restricts to zero. In each alias class use one representative and
    # write h as differences of characters with the same restricted sign.
    reps={};image={};normals=tuple(s for s,b in row)
    eq=tuple(value(normals,1<<l) for l in range(n))
    delta=tuple((-1)**(b^int(i==j)) for i,(s,b) in enumerate(row))
    base=sum(1+len(G)*(len(G)-1)//2 for G in F[:e])+1
    pair_id={pair:base+i for i,pair in enumerate(combinations(range(len(row)),2))}
    for s,w in h.items():
        q=value(V,s);sgn=(-1)**((s&a).bit_count()%2);add(image,{q:w},sgn,p)
        t=reps.setdefault(q,s)
        if s==t:continue
        Q=canon((v,((s^t)>>l)&1) for l,v in enumerate(eq));assert Q is not None
        choice=chart(len(row),Q)[0];I=[i for i in range(len(row)) if choice>>i&1]
        suffix=1
        for i in I:suffix*=delta[i]
        prefix=t
        for i in I:
            suffix*=delta[i]
            if i!=j:
                k=pair_id[tuple(sorted((i,j)))];c=-(-1)**row[i][1]*suffix*w
                # (2*x_j)*(chi_si-delta_i) = -eps_i*(4*x_j*x_i).
                add(out,{(k,prefix):c},1,p)
            prefix^=row[i][0];B.pay('character_lift_telescope')
    assert not image
    certificate=tuple((k,t,c) for (k,t),c in sorted(out.items()))
    assert verify_onehot_exclusion(F,e,j,certificate,p,B)
    return certificate


def transport_onehot_exclusion(certificate,V,a,p,B):
    """Pull a flat proof to the actual rechart, keeping original generator IDs."""
    C={}
    for k,t,c in certificate:
        B.pay('character_lift_transport',1+len(V))
        add(C,{(k,value(V,t)):c},(-1)**((t&a).bit_count()%2),p)
    return tuple((k,t,c) for (k,t),c in sorted(C.items()))


def adaptive_reopen(n,F,basis,p,B,nodes=32,degree=0,max_pivots=256,learned=None,certificates=None):
    """Bounded original-row partition with child-local character strengthening.

    Return (witness, decisive). Only checked root-child exclusions may be
    exported as (row, occurrence). Optional certificates request a standalone
    replayable proof when a local character refutation can be independently
    reproduced under the same cap. UNKNOWN is never learned as exclusion.
    """
    assert nodes>=0 and max_pivots>=0 and degree in (-1,0,1,2)
    original=F;left=nodes
    def valid(J,x):
        B.pay('character_adaptive_verify',1+sum(map(len,J)))
        return all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in J)
    def visit(J,K,u,V):
        nonlocal left
        if not left:return None,False
        left-=1;B.pay('character_adaptive_node')
        if 0 in K:return None,True
        if valid(J,0):return u,True
        if degree>=0 and len(V)<n:K=extend_character_span(J,K,p,B,degree,max_pivots)
        if 0 in K:
            B.pay('character_adaptive_local_empty');return None,True
        e=min((i for i,G in enumerate(J) if sum(b for s,b in G)!=1),key=lambda i:len(J[i]))
        G=J[e];candidates=[];d=len(V)
        def record(j,R=None):
            if d!=n:return
            if learned is not None:
                learned.append((e,j));B.pay('character_adaptive_learned')
            if certificates is not None and R is not None and degree>=0:
                proof,empty=eliminate(R,source_shifts(R,degree,B),p,B,max_pivots=max_pivots)
                if empty:
                    C=lift_onehot_exclusion(n,J,e,j,compact(proof,B),p,B)
                    assert C is not None
                    certificates.append((e,j,C));B.pay('character_adaptive_lifted',1+len(C))
        for j in range(len(G)):
            B.pay('character_adaptive_pattern',1+len(G))
            H=canon((s,b^int(i==j)) for i,(s,b) in enumerate(G))
            if H is None:record(j);continue
            a,W=chart(d,H);assert len(W)<d
            if valid(J,a):return lift(u,V,a),True
            B.pay('character_adaptive_score',1+sum(map(len,J)))
            score=sum(abs(sum(b^((s&a).bit_count()%2) for s,b in A)-1) for A in J)
            candidates.append(((score,len(W),j),a,W))
        for (_,_,j),a,W in sorted(candidates):
            if not left:return None,False
            Q=restrict_character_span(K,W,a,p,B)
            if 0 in Q:
                B.pay('character_adaptive_projected_empty');record(j);continue
            B.pay('character_adaptive_image',1+sum(map(len,J))*(1+len(W)))
            R=tuple(tuple((value(W,s),b^((s&a).bit_count()%2)) for s,b in A) for A in J)
            x,done=visit(R,Q,lift(u,V,a),tuple(lift(0,V,w) for w in W))
            if x is not None:return x,True
            if not done:return None,False
            B.pay('character_adaptive_backtrack');record(j,R)
        return None,True
    x,done=visit(F,basis,0,tuple(1<<i for i in range(n)))
    if x is not None:assert done and valid(original,x)
    return x,done


def restriction_reopen(n,F,basis,p,B,steps):
    """One-path original-row restriction, sharing the replayed proof span.

    Empty projected spans are not feasibility evidence. A constant in the
    projected span excludes that child; failure of greedy discovery is UNKNOWN.
    Returns only an independently verified witness, or None.
    """
    assert steps>=0
    original=F;origin=0;V0=tuple(1<<i for i in range(n))
    if 0 in basis:return None
    for step in range(min(steps,n)+1):
        B.pay('character_path_verify',1+sum(map(len,F)))
        bad=[G for G in F if sum(b for s,b in G)!=1]
        if not bad:
            assert all(sum(b^((s&origin).bit_count()%2) for s,b in G)==1 for G in original)
            return origin
        if step==min(steps,n):return None
        G=min(bad,key=len);candidates=[];best=None
        for j in range(len(G)):
            B.pay('character_path_branch',1+len(G))
            H=canon((s,b^int(i==j)) for i,(s,b) in enumerate(G))
            if H is None:continue
            a,V=chart(len(V0),H);assert len(V)<len(V0)
            B.pay('character_path_score',1+sum(map(len,F)))
            # Check original row residual at the branch origin before mapping.
            score=sum(abs(sum(b^((s&a).bit_count()%2) for s,b in J)-1) for J in F)
            if not score:
                x=lift(origin,V0,a)
                assert all(sum(b^((s&x).bit_count()%2) for s,b in J)==1 for J in original)
                return x
            candidates.append(((score,len(V),j),a,V))
        for key,a,V in sorted(candidates):
            Q=restrict_character_span(basis,V,a,p,B)
            if 0 in Q:
                B.pay('character_path_excluded');continue
            B.pay('character_path_image',1+sum(map(len,F))*(1+len(V)))
            R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in J) for J in F)
            best=(key,a,V,R,Q);break
        if best is None:return None
        _,a,V,F,basis=best
        origin=lift(origin,V0,a);V0=tuple(lift(0,V0,v) for v in V)
        B.pay('character_path_step')
    return None


def demand_character_close(n,F,H,B,degree=1,p=3,max_pivots=4096,quotient_cap=0,path_steps=0,section_cap=0,adaptive_nodes=0,adaptive_degree=0):
    """Sound original affine refinement and optional original witness.

    Share one replayed elimination span across both consumers. None carrier
    certifies empty; a carrier without witness is not a feasibility decision.
    """
    B.pay('character_demand',1+len(H));P=canon(H)
    if P is None:return None,None
    u,V=chart(n,P);B.pay('character_pullback',1+sum(len(G) for G in F)*(1+len(V)))
    R=tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)
    reps={0:0}
    for G in F:
        for s,b in G:reps.setdefault(value(V,s),s)
    freq=tuple(reps);eq=tuple(value(freq,1<<j) for j in range(len(V)))
    proof,rel,zero,basis=character_relation_span(R,source_shifts(R,degree,B),freq,p,B,max_pivots)
    if not span_accepts_relations(basis,rel,zero,p,B):raise AssertionError('invalid character consequence')
    Q=relation_pins(rel,zero,p)
    if Q is None:return None,None
    pins=[]
    for s,b in Q:
        B.pay('character_reopen',1+len(freq)*max(1,len(V)))
        C=canon((v,(s>>j)&1) for j,v in enumerate(eq));assert C is not None
        a=lift(0,[reps[t] for t in freq],chart(len(freq),C)[0])
        pins.append((a,b^((a&u).bit_count()%2)))
    C=canon(P+tuple(pins));assert C is not None
    if not quotient_cap and not path_steps and not section_cap and not adaptive_nodes:return C,None
    x=chart(n,C)[0]
    B.pay('character_pin_verify',1+sum(map(len,F)))
    if all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F):return C,x
    z=lazy_section(len(V),R,basis,p,B,section_cap) if section_cap else None
    if z is None and (path_steps or adaptive_nodes):
        a,W=chart(len(V),Q)
        B.pay('character_path_pins',1+sum(map(len,R))*(1+len(W)))
        J=tuple(tuple((value(W,s),b^((s&a).bit_count()%2)) for s,b in G) for G in R)
        K=restrict_character_span(basis,W,a,p,B) if Q else basis
        if 0 in K:return None,None
        y=restriction_reopen(len(W),J,K,p,B,path_steps) if path_steps else None
        if y is None and adaptive_nodes:
            learned=[]
            y,done=adaptive_reopen(len(W),J,K,p,B,adaptive_nodes,adaptive_degree,min(max_pivots,256),learned)
            if done and y is None:return None,None
            # Root child exclusions apply throughout the refined parent.
            # Stable row/occurrence IDs recover the actual original equations.
            D=canon(C+tuple(F[e][j] for e,j in learned))
            if D is None:return None,None
            B.pay('character_adaptive_rank',len(D)-len(C));C=D
        if y is not None:z=lift(a,W,y)
    if z is None and quotient_cap:z=quotient_reopen(len(V),R,basis,p,B,quotient_cap)
    if z is not None:
        x=lift(u,V,z)
        assert all((s&x).bit_count()%2==b for s,b in C)
        assert all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
        return C,x
    return C,None


def demand_refinement(n,F,H,B,degree=1,p=3,max_pivots=4096):
    return demand_character_close(n,F,H,B,degree,p,max_pivots)[0]


def test_character_consequences():
    from random import Random
    from check_pnp_affine_normal_components import satisfies, Exhausted
    def valid(F,x):return all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
    # Two different normals forced equal without either individual normal fixed.
    F=(((1,0),(2,1)),)
    P=character_consequences(F,(0,),range(4),3,Budget(10000))
    assert P==((3,0),),P
    assert demand_refinement(2,F,(),Budget(10000),degree=0)==((3,0),)
    # Full character image recovers exactly every affine equation true on solutions.
    rng=Random(36927);full=bounded=empty=rank=transport=0
    for n in range(6):
     for _ in range(60):
      F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(6))) for i in range(rng.randrange(6)))
      T=[x for x in range(1<<n) if valid(F,x)]
      for p in (3,5,7):
       P=character_consequences(F,range(1<<n),range(1<<n),p,Budget(5000000))
       assert (P is None)==(not T)
       if T:
        Q=canon((s,(s&T[0]).bit_count()%2) for s in range(1<<n) if len({(s&x).bit_count()%2 for x in T})==1)
        assert P==Q,(F,P,Q);rank+=len(P)
       else:empty+=1
       full+=1
      H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
      if H is None:continue
      T=[x for x in T if satisfies(x,H,())]
      P=demand_refinement(n,F,H,Budget(5000000),degree=1)
      assert (P is not None or not T) and (P is None or all(satisfies(x,P,()) for x in T))
      assert P is None or canon(P+H)==P
      bounded+=1
      a=rng.randrange(1<<n);shift=lambda G:tuple((s,b^((s&a).bit_count()%2)) for s,b in G)
      Q=demand_refinement(n,tuple(shift(G) for G in F),shift(H),Budget(5000000),degree=1)
      assert (Q is None or all(satisfies(x^a,Q,()) for x in T)) and (Q is not None or not T)
      transport+=1
    try:demand_refinement(2,(((1,0),(2,1)),),(),Budget(0));assert False
    except Exhausted:pass
    # Full pair-hull closure is inconclusive on this inhabited affine source.
    F=(((47,1),(29,1),(74,0),(21,0)),((68,0),(107,1),(84,0)),((33,0),(48,1),(99,0)))
    from check_pnp_normal_boundary_join import orth,span
    P=();T=list(range(128))
    while True:
        rows=[]
        for A,C in combinations(F,2):
            S=[z for z in T if valid((A,C),z)];assert S
            rows.extend((s,(s&S[0]).bit_count()%2) for s in orth(7,span(z^S[0] for z in S)))
        Q=canon(P+tuple(rows));assert Q is not None
        if Q==P:break
        P=Q;T=[z for z in T if satisfies(z,P,())]
    assert len(P)==3 and not valid(F,chart(7,P)[0])
    Q=demand_refinement(7,F,P,Budget(1000000));assert len(Q)==5
    assert [z for z in range(128) if valid(F,z)]==[57,89,109]
    assert all(satisfies(z,Q,()) for z in (57,89,109)) and valid(F,chart(7,Q)[0])
    # A truncated elimination is still safe; an absent relation is not exclusion.
    for cap in (0,1,2,4):
        Q=demand_refinement(7,F,P,Budget(1000000),max_pivots=cap)
        assert Q is not None and all(satisfies(z,Q,()) for z in (57,89,109))
    assert not verify(F,None,3)
    print('character_consequences',dict(full=full,empty=empty,rank=rank,bounded=bounded,transport=transport), 'pair_hull_rank_3_to_5 PASS')


def test_constructive_character_quotient():
    from random import Random
    from check_pnp_affine_normal_components import Exhausted
    rng=Random(369261127);full=bounded=transported=0
    for n in range(7):
        for _ in range(60):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))) for j in range(rng.randrange(7)))
            valid=lambda x:all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
            truth=[x for x in range(1<<n) if valid(x)]
            for p in (3,5,7):
                B=Budget(10000000)
                proof,rel,zero=character_relations(F,range(1<<n),range(1<<n),p,B)
                assert verify_relations(F,proof,rel,zero,p,B) and (relation_pins(rel,zero,p) is not None)==bool(truth)
                basis=replay_span(F,proof,p,B);x=quotient_reopen(n,F,basis,p,B,1<<n)
                assert (x is not None)==bool(truth) and (x is None or valid(x))
                if truth:
                    P=relation_pins(rel,zero,p)
                    assert P==canon((s,(s&truth[0]).bit_count()%2) for s in range(1<<n) if all((s&(x^truth[0])).bit_count()%2==0 for x in truth))
                    if rel:
                        s,t,c=rel[0];assert not verify_relations(F,proof,((s,t,-c%p),),None,p,B)
                a=rng.randrange(1<<n);V=tuple(rng.randrange(1<<n) for i in range(rng.randrange(n+1)))
                R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
                r,z=transport_relations(rel,zero,V,a,p)
                assert verify_relations(R,transport_proof(proof,V,a,p,B),r,z,p,B)
                full+=1;transported+=1
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
            if H is None:continue
            T=[x for x in truth if all((s&x).bit_count()%2==b for s,b in H)]
            for degree in (0,1):
                P,w=demand_character_close(n,F,H,Budget(10000000),degree=degree,max_pivots=32,quotient_cap=8)
                if P is None:assert not T and w is None
                else:
                    assert canon(P+H)==P and all(all((s&x).bit_count()%2==b for s,b in P) for x in T)
                    assert w is None or w in T
                bounded+=1
    S=[(6,9,17),(2,9,13),(2,14,16),(0,5,15),(3,6,13),(1,13,15),(10,13,17),(0,4,8),(6,12,17),(3,8,12),(0,5,16),(4,7,9),(7,11,14),(10,12,17),(0,5,17),(1,3,4),(5,9,16),(6,10,16),(7,10,11),(1,2,13),(1,7,12),(4,7,15),(8,11,14),(1,8,14),(3,4,15),(5,10,11),(2,11,15),(2,9,12),(6,8,14),(0,3,16)]
    R=tuple(sum(1<<j for j,s in enumerate(S) if i in s) for i in range(18))
    u,V=chart(30,canon((r,1) for r in R))
    F=tuple(tuple((value(V,1<<j),u>>j&1) for j in range(30) if r>>j&1) for r in R)
    B=Budget(10000000);P,w=demand_character_close(len(V),F,(),B,quotient_cap=64)
    assert len(P)==9 and w is not None and all((lift(u,V,w)&r).bit_count()==1 for r in R)
    assert B.stats['character_module_dimension']==4
    Q,w0=demand_character_close(len(V),F,(),Budget(10000000),quotient_cap=1)
    assert Q==P and w0 is None
    B=Budget(10000000);Q,w0=demand_character_close(len(V),F,(),B,section_cap=2)
    assert Q==P and w0 is not None and lift(u,V,w0)==25429250
    assert B.stats['character_section_verify']>0 and not B.stats['character_module_edge']
    Q,w0=demand_character_close(len(V),F,(),Budget(10000000),section_cap=1,path_steps=30)
    assert Q==P and w0 is not None and all((lift(u,V,w0)&r).bit_count()==1 for r in R)
    # A non-sign proportionality is itself an exact contradiction over F5.
    A=(((4,0),(6,1),(3,1),(1,0)),)
    proof,rel,zero=character_relations(A,(0,),range(8),5,Budget(1000000))
    assert zero is None and any(c not in (1,4) for s,t,c in rel)
    assert verify_relations(A,proof,rel,zero,5,Budget(1000000)) and relation_pins(rel,zero,5) is None
    try:demand_character_close(len(V),F,(),Budget(0),quotient_cap=64);assert False
    except Exhausted:pass
    print(dict(constructive_full=full,constructive_bounded=bounded,constructive_transport=transported,module_control='PASS'))


def test_character_restriction_path():
    from random import Random
    from check_pnp_affine_normal_components import Exhausted
    rng=Random(261136928);full=partial=transport=0
    for n in range(7):
        for _ in range(100):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))) for j in range(rng.randrange(7)))
            valid=lambda x:all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
            T=[x for x in range(1<<n) if valid(x)]
            for p in (3,5,7):
                B=Budget(10000000);proof,_=eliminate(F,range(1<<n),p,B);basis=replay_span(F,proof,p,B)
                x=restriction_reopen(n,F,basis,p,B,n)
                assert (x is not None)==bool(T) and (x is None or x in T);full+=1
                if T:
                    a=rng.randrange(1<<n);V=tuple(1<<i for i in range(n) if rng.randrange(2))
                    Q=restrict_character_span(basis,V,a,p,B)
                    assert (0 in Q)==(not any(valid(lift(a,V,y)) for y in range(1<<len(V))))
                    if 0 not in Q:
                        R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
                        pp,_=eliminate(R,range(1<<len(V)),p,B);K=replay_span(R,pp,p,B)
                        assert len(K)==len(Q) and all(not quotient_normal(A,K,p,B) for A in Q.values())
                    transport+=1
                proof,_=eliminate(F,(0,),p,B,max_pivots=8);basis=replay_span(F,proof,p,B)
                x=restriction_reopen(n,F,basis,p,B,n)
                assert x is None or x in T;partial+=1
    for r in (4,8,16,32,64):
        n=2*r+1;F=tuple(((1,0),(1<<(2*i+1),0),(1<<(2*i+2),0)) for i in range(r))
        B=Budget(10000000);proof,_=eliminate(F,(0,),3,B);basis=replay_span(F,proof,3,B)
        assert quotient_reopen(n,F,basis,3,B,8) is None
        assert restriction_reopen(n,F,basis,3,B,n)==1
        assert restriction_reopen(n,F,basis,3,B,0) is None
    # Inhabited control: a capped span can leave a spurious child alive.
    F=(((16,1),(9,0),(14,1),(13,1),(3,0)),((27,1),(25,1)))
    B=Budget(10000000);proof,_=eliminate(F,(0,),3,B,max_pivots=8);basis=replay_span(F,proof,3,B)
    assert [x for x in range(32) if all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)]==[15,19]
    assert restriction_reopen(5,F,basis,3,B,5) is None
    proof,_=eliminate(F,range(32),3,B);basis=replay_span(F,proof,3,B)
    assert restriction_reopen(5,F,basis,3,B,5) in (15,19)
    try:restriction_reopen(1,(((1,0),),),{},3,Budget(0),1);assert False
    except Exhausted:pass
    print(dict(restriction_full=full,restriction_partial=partial,restriction_transport=transport,star_controls='PASS'))


def test_character_section():
    from random import Random
    from check_pnp_affine_normal_components import Exhausted
    def valid(F,x):return all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
    def ev(A,x,p):return sum(w*(-1)**((s&x).bit_count()%2) for s,w in A.items())%p
    rng=Random(36928);full=partial=got=zero=transport=products=0
    for n in range(7):
        for _ in range(60):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(7))) for i in range(rng.randrange(7)))
            T=[x for x in range(1<<n) if valid(F,x)]
            for p in (3,5,7):
                B=Budget(10000000);proof,_=eliminate(F,range(1<<n),p,B);basis=replay_span(F,proof,p,B)
                w=lazy_section(n,F,basis,p,B,1<<n)
                assert (w is not None)==bool(T) and (w is None or w in T);full+=1
                proof,_=eliminate(F,source_shifts(F,0),p,B,max_pivots=8);basis=replay_span(F,proof,p,B)
                w=lazy_section(n,F,basis,p,B,4);assert w is None or w in T;partial+=1;got+=w is not None
                if 0 not in basis:
                    q={rng.randrange(1<<n):1};s=rng.randrange(1<<n);b=rng.randrange(2)
                    A=section_project(q,s,b,basis,p,B)
                    for x in T:
                        assert ev(A,x,p)==(1-(-1)**(b+(s&x).bit_count()%2))*ev(q,x,p)%p;products+=1
                    if not A:assert all((b^((s&x).bit_count()%2))==0 for x in T);zero+=1
                a=rng.randrange(1<<n);V=tuple(rng.randrange(1<<n) for i in range(rng.randrange(n+1)))
                R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
                C=replay_span(R,transport_proof(proof,V,a,p,B),p,B)
                z=lazy_section(len(V),R,C,p,B,4);assert z is None or valid(F,lift(a,V,z));transport+=1
    for n in (8,16,32,64,128):
        F=(tuple((1<<j,0) for j in range(n)),)
        B=Budget(10000000);proof,empty=eliminate(F,(0,),3,B);assert not empty;basis=replay_span(F,proof,3,B)
        assert quotient_reopen(n,F,basis,3,B,4) is None
        D=Budget(10000000);x=lazy_section(n,F,basis,3,D,4);assert x is not None and valid(F,x)
        assert D.stats['character_section_retained']==2
    F=(((1,0),(2,0)),((2,0),))
    assert valid(F,2) and lazy_section(2,F,{},3,Budget(10000),4) is None
    try:lazy_section(2,F,{},3,Budget(0),4);assert False
    except Exhausted:pass
    print(dict(section_full=full,section_partial=partial,section_verified=got,section_products=products,section_zero=zero,section_transport=transport))
    from collections import Counter
    for seed in (3692819,3692820):
        rng=Random(seed);stats=Counter();cost=Counter()
        for _ in range(240):
            n=rng.choice((6,8,10));target=rng.randrange(1<<n);F=[]
            for i in range(rng.randrange(3,8)):
                G=rng.sample(range(1,1<<n),rng.randrange(3,7));j=rng.randrange(len(G))
                F.append(tuple((a,((a&target).bit_count()%2)^int(k==j)) for k,a in enumerate(G)))
            F=tuple(F);assert valid(F,target);B=Budget(5000000)
            proof,empty=eliminate(F,source_shifts(F,0),3,B,max_pivots=64);assert not empty;basis=replay_span(F,proof,3,B)
            M=Budget(5000000);x=quotient_reopen(n,F,basis,3,M,4)
            P=Budget(5000000);w=restriction_reopen(n,F,basis,3,P,n)
            L=Budget(5000000);y=lazy_section(n,F,basis,3,L,4)
            for z in (x,w,y):assert z is None or valid(F,z)
            stats['module']+=x is not None;stats['path']+=w is not None;stats['lazy']+=y is not None
            stats['union']+=w is not None or y is not None or x is not None
            stats['only_lazy']+=x is None and w is None and y is not None
            stats['only_path']+=x is None and y is None and w is not None
            for key,K in [('module',M),('path',P),('lazy',L)]:cost[key]+=sum(K.stats.values())
            cost['hybrid']+=sum(L.stats.values())+(sum(P.stats.values()) if y is None else 0)
        assert stats['only_lazy']>0 and cost['hybrid']<cost['path']
        print('section_holdout',seed,dict(stats),dict(cost))


def test_character_adaptive():
    from random import Random
    from collections import Counter
    from check_pnp_affine_normal_components import Exhausted, satisfies
    def valid(F,x):return all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
    F=(((16,1),(9,0),(14,1),(13,1),(3,0)),((27,1),(25,1)))
    B=Budget(1000000);proof,_=eliminate(F,(0,),3,B,max_pivots=8);K=replay_span(F,proof,3,B)
    assert restriction_reopen(5,F,K,3,B,5) is None
    for degree in (-1,0,1):
        C=Budget(1000000);x,done=adaptive_reopen(5,F,K,3,C,16,degree,64)
        assert done and x in (15,19)
        assert C.stats['character_adaptive_backtrack']>0
        if degree>=0:assert C.stats['character_adaptive_local_empty']>0
    assert adaptive_reopen(5,F,K,3,B,0)==(None,False)
    rng=Random(36929);count=Counter()
    for n in range(7):
        for _ in range(60):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))) for j in range(rng.randrange(7)))
            T=[x for x in range(1<<n) if valid(F,x)]
            for p in (3,5,7):
                B=Budget(10000000);proof,_=eliminate(F,(0,),p,B,max_pivots=8);K=replay_span(F,proof,p,B)
                D=extend_character_span(F,K,p,B,1,64)
                assert all(sum(w*(-1)**((s&x).bit_count()%2) for s,w in A.items())%p==0 for A in D.values() for x in T)
                for cap in (1,4,128):
                    x,done=adaptive_reopen(n,F,K,p,B,cap,1,32)
                    assert x is None or x in T
                    assert not done or (x is not None)==bool(T)
                    if cap==128:assert done
                    count['checks']+=1;count['unknown']+=not done;count['witness']+=x is not None;count['empty']+=done and x is None
                a=rng.randrange(1<<n);V=tuple(1<<i for i in range(n) if rng.randrange(2))
                R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
                D=restrict_character_span(K,V,a,p,B);x,done=adaptive_reopen(len(V),R,D,p,B,128,1,32)
                U=[y for y in range(1<<len(V)) if valid(F,lift(a,V,y))]
                assert done and (x is not None)==bool(U) and (x is None or x in U)
                count['transport']+=1
    print('adaptive',dict(count))
    for seed in (3692819,3692820):
        rng=Random(seed);stats=Counter();cost=Counter()
        for _ in range(240):
            n=rng.choice((6,8,10));target=rng.randrange(1<<n);F=[]
            for i in range(rng.randrange(3,8)):
                G=rng.sample(range(1,1<<n),rng.randrange(3,7));j=rng.randrange(len(G))
                F.append(tuple((a,((a&target).bit_count()%2)^int(k==j)) for k,a in enumerate(G)))
            F=tuple(F);B=Budget(5000000);proof,empty=eliminate(F,(0,),3,B,max_pivots=64);assert not empty;K=replay_span(F,proof,3,B)
            y=lazy_section(n,F,K,3,Budget(5000000),4);w=restriction_reopen(n,F,K,3,Budget(5000000),n)
            stats['base']+=y is not None or w is not None
            if y is not None or w is not None:continue
            stats['stalled']+=1
            for degree in (-1,0,1):
                D=Budget(5000000);x,done=adaptive_reopen(n,F,K,3,D,16,degree,64)
                assert x is None or valid(F,x);assert not done or x is not None
                stats['recover'+str(degree)]+=x is not None;cost[str(degree)]+=sum(D.stats.values())
        assert stats['stalled']==stats['recover-1']==stats['recover0']==stats['recover1']
        print('adaptive_holdout',seed,dict(stats),dict(cost))
    rng=Random(36930);stats=Counter()
    for n in (5,6,7,8):
        for _ in range(100):
            F=tuple(tuple((rng.randrange(1,1<<n),rng.randrange(2)) for j in range(rng.randrange(3,7))) for i in range(rng.randrange(3,8)))
            T=[x for x in range(1<<n) if valid(F,x)]
            B=Budget(10000000);proof,_=eliminate(F,(0,),3,B,max_pivots=8);K=replay_span(F,proof,3,B)
            for degree in (-1,0,1):
                C=Budget(10000000);x,done=adaptive_reopen(n,F,K,3,C,4,degree,64)
                assert x is None or x in T;assert not done or bool(T)==(x is not None)
                stats['done'+str(degree)]+=done;stats['cost'+str(degree)]+=sum(C.stats.values())
    assert stats['done-1']==151 and stats['done0']==335 and stats['done1']==338
    print('adaptive_four_node',dict(stats))
    rng=Random(3692821);checks=empty=verified=unknown=0
    for n in range(7):
        for _ in range(80):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(6))) for i in range(rng.randrange(6)))
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
            if H is None:continue
            T=[x for x in range(1<<n) if valid(F,x) and satisfies(x,H,())]
            for degree in (0,1):
                P,x=demand_character_close(n,F,H,Budget(5000000),degree=degree,max_pivots=24,section_cap=4,path_steps=n,adaptive_nodes=16)
                if P is None:assert not T and x is None;empty+=1
                else:
                    assert canon(P+H)==P and all(satisfies(y,P,()) for y in T)
                    assert x is None or x in T
                    verified+=x is not None;unknown+=x is None
                checks+=1
    assert (checks,empty,verified,unknown)==(990,680,310,0)
    try:adaptive_reopen(1,(((1,0),),),{},3,Budget(0));assert False
    except Exhausted:pass
    print('adaptive_demand',checks,empty,verified,unknown)


def test_character_parent_learning():
    from random import Random
    from collections import Counter
    from check_pnp_affine_normal_components import Exhausted
    rng=Random(369261129);certified=0
    for n in range(1,8):
        for _ in range(100):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(1,7))) for j in range(rng.randrange(1,6)))
            valid=lambda x:all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
            T=[x for x in range(1<<n) if valid(x)]
            e=rng.randrange(len(F));j=rng.randrange(len(F[e]));row=F[e]
            H=canon((s,b^int(i==j)) for i,(s,b) in enumerate(row))
            if H is None:continue
            a,V=chart(n,H);R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
            for p in (3,5,7):
                B=Budget(10000000);proof,empty=eliminate(R,range(1<<len(V)),p,B)
                assert empty==(not any(all((s&x).bit_count()%2==b for s,b in H) for x in T))
                if not empty:continue
                C=lift_onehot_exclusion(n,F,e,j,compact(proof,B),p,B);assert C is not None
                assert all((row[j][1]^((row[j][0]&x).bit_count()%2))==0 for x in T)
                if C:
                    k,t,c=C[0];G=tuple(generators(F,p))
                    if G[k]:assert not verify_onehot_exclusion(F,e,j,((k,t,-c%p),)+C[1:],p,B)
                certified+=1
    assert certified==798
    rng=Random(36929);stats=Counter()
    for n in range(8):
        for _ in range(100):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))) for j in range(rng.randrange(7)))
            T=[x for x in range(1<<n) if all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)]
            for p in (3,5,7):
                B=Budget(10000000);proof,_=eliminate(F,(0,),p,B,max_pivots=8);K=replay_span(F,proof,p,B)
                for cap in (1,4,128):
                    for degree in (-1,0):
                        B=Budget(10000000);L=[];C=[]
                        y,done=adaptive_reopen(n,F,K,p,B,cap,degree,32,L,C)
                        assert y is None or y in T;assert not done or bool(T)==(y is not None)
                        assert all(all(not (F[e][j][1]^((F[e][j][0]&x).bit_count()%2)) for e,j in L) for x in T)
                        if cap==128:assert done
                        for e,j,P in C:
                            assert (e,j) in L and verify_onehot_exclusion(F,e,j,P,p,B)
                            a=rng.randrange(1<<n);V=tuple(1<<i for i in range(n) if rng.randrange(2))
                            R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
                            assert verify_onehot_exclusion(R,e,j,transport_onehot_exclusion(P,V,a,p,B),p,B)
                            stats['transport']+=1
                        stats['comparisons']+=1;stats['pins']+=len(L);stats['unknown']+=not done
                        stats['lifted']+=len(C);stats['inhabited_pins']+=len(L) if T else 0
    assert stats['comparisons']==14400
    F=(((16,1),(9,0),(14,1),(13,1),(3,0)),((27,1),(25,1)))
    B=Budget(10000000);proof,_=eliminate(F,(0,),3,B,max_pivots=8);K=replay_span(F,proof,3,B)
    assert restriction_reopen(5,F,K,3,B,5) is None
    L=[];C=[]
    assert adaptive_reopen(5,F,K,3,B,0,0,32,L,C)==(None,False) and not L and not C
    x,done=adaptive_reopen(5,F,K,3,B,4,0,32,L,C)
    assert x in (15,19) and done and (1,0) in L and C
    try:adaptive_reopen(1,(((1,0),),),{},3,Budget(0),1);assert False
    except Exhausted:pass
    print('character_parent_learning',certified,dict(stats))


def main():
    test_character_parent_learning()
    test_character_adaptive()
    test_character_section()
    test_character_restriction_path()
    test_constructive_character_quotient()
    test_character_consequences()
    from random import Random
    from check_pnp_affine_normal_components import Exhausted
    rng=Random(3692611);full=bounded=exclusions=translated=transported=0
    for n in range(6):
        for _ in range(60):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(7))) for i in range(rng.randrange(7)))
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
            if H is None:continue
            u,V=chart(n,H)
            R=tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)
            valid=lambda x:all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
            truth=any(valid(lift(u,V,z)) for z in range(1<<len(V)))
            for p in (3,5,7):
                B=Budget(3000000);Q=exclude(R,range(1<<len(V)),p,B)
                assert (Q is None)==truth;full+=1
                if Q is not None:
                    Q=compact(Q,B);assert verify(R,Q,p,B=B);exclusions+=1
                    a0=rng.randrange(1<<len(V));W=tuple(1<<i for i in range(len(V)) if rng.randrange(2))
                    R0=tuple(tuple((value(W,s),b^((s&a0).bit_count()%2)) for s,b in G) for G in R)
                    assert verify(R0,transport_proof(Q,W,a0,p,B),p,B=B);transported+=1
            got=demand_exclusion(n,F,H,Budget(3000000));assert not got or not truth;bounded+=1
            a=rng.randrange(1<<n)
            shift=lambda G:tuple((s,b^((s&a).bit_count()%2)) for s,b in G)
            assert demand_exclusion(n,tuple(shift(G) for G in F),shift(H),Budget(3000000))==got
            translated+=1
    # Actual original empty source surviving parity-capacity and pair-hull closure.
    S=[(5,13,17),(5,14,16),(3,10,17),(0,2,16),(3,4,16),(1,10,12),(0,7,15),(6,7,10),(1,12,13),(4,5,13),(1,3,12),(0,4,6),(8,10,17),(3,7,9),(1,14,15),(9,12,15),(2,13,16),(2,12,17),(2,5,15),(6,7,8),(6,7,14),(8,11,17),(4,11,15),(5,8,11),(2,3,9),(6,9,13),(9,10,11),(0,1,16),(0,4,14),(8,11,14)]
    R=tuple(sum(1<<j for j,s in enumerate(S) if i in s) for i in range(18));u,V=chart(30,canon((r,1) for r in R))
    F=tuple(tuple((value(V,1<<j),u>>j&1) for j in range(30) if r>>j&1) for r in R)
    assert not any(all((lift(u,V,z)&r).bit_count()==1 for r in R) for z in range(1<<len(V)))
    assert exclude(F,(0,),3,Budget(3000000)) is None
    assert exclude(F,source_shifts(F),3,Budget(3000000),pairs=False) is None
    B=Budget(3000000);Q=exclude(F,source_shifts(F),3,B);assert Q is not None
    generated=len(Q);Q=compact(Q,B);assert verify(F,Q,3,B=B)
    j,t,ops,c=Q[-1];bad=Q[:-1]+((j,t,ops,c%2+1),)
    assert not verify(F,bad,3)
    assert demand_exclusion(len(V),F,(),Budget(3000000))
    try:demand_exclusion(len(V),F,(),Budget(0));assert False
    except Exhausted:pass
    print('original_30',len(V),len(source_shifts(F)),generated,len(Q),sum(B.stats.values()))
    print(dict(full=full,exclusions=exclusions,bounded=bounded,translated=translated,transported=transported,controls='PASS'))


if __name__=='__main__':main()
