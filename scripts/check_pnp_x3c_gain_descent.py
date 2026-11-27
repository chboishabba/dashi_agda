"""Exact original X3C gain descent: integer image, capacity, quotient and component witnesses."""
from itertools import combinations
from random import Random
from sympy import Matrix, ones
from sympy.matrices.normalforms import hermite_normal_form
from check_pnp_affine_normal_components import (bits, canon, chart, lift, split,
    reopen, satisfies, Budget, Exhausted)
from check_pnp_normal_boundary_join import value
from check_pnp_exact_cover_pair_hull import incidence, cover, close, row_capacity
from check_pnp_adaptive_signed_escape import add, point
from check_pnp_partial_quotient import positive_point
from check_pnp_signed_moment_filter import moment_point
from check_pnp_signed_quotient_minimum import minimum


def integer_image(A,b,B):
    """Exact mod2 image of integer solutions, not binary feasibility."""
    m,n=A.shape;B.pay('hnf_input',1+m*(n+1));H=hermite_normal_form(A)
    r=H.cols
    if not r:return () if not any(b) else None
    I=list(H.T.rref()[1]);D=H[I,:].inv()*A[I,:];c=H[I,:].inv()*b[I,:]
    B.pay('lattice_coordinates',1+r*(n+1))
    assert H*D==A and all(a.q==1 for a in D)
    if H*c!=b or any(a.q!=1 for a in c):return None
    P=canon((sum((int(D[i,j])&1)<<j for j in range(n)),int(c[i])&1) for i in range(r))
    assert P is not None and len(P)==r
    return P


def capacity(n,R,k,B):
    J=row_capacity(n,R,B)
    if len(J)<k:return None
    if len(J)>k:return ()
    # Tight hitting cover: each selected column meets exactly one hitting row.
    B.pay('capacity_slack',1+n*len(J))
    return tuple((1<<i,0) for i in range(n) if sum((R[j]>>i)&1 for j in J)>1)


def quotient(n,P,x,B):
    """Return removal-only trade or independent-incumbent addition kernel lifts."""
    S=tuple(bits(x));U=tuple(bits(((1<<n)-1)^x));A=[a for a,b in P];E={}
    def reduce(a):
        z=0
        for k in sorted(E,reverse=True):
            if a>>k&1:v,c=E[k];a^=v;z^=c
        return a,z
    for i in S:
        B.pay('incumbent_column');a,z=reduce(value(A,1<<i))
        if not a:return z^(1<<i),None,None,None
        E[a.bit_length()-1]=(a,z^(1<<i))
    Q=[];R=[]
    for i in U:
        B.pay('addition_column');a,z=reduce(value(A,1<<i));Q.append(a);R.append(z)
    H=canon((value(Q,1<<j),0) for j in range(len(A)))
    _,K=chart(len(U),H)
    V=tuple(lift(0,R,t)^lift(0,[1<<i for i in U],t) for t in K)
    assert all(satisfies(x^v,P,()) for v in V)
    return None,U,K,V


def gain_chart(n,x,V,B):
    M={}
    for i in range(n):
        B.pay('gain_term',1+len(V));a=value(V,1<<i)
        if a:add(M,((a,1),),1 if x>>i&1 else -1)
    return M


def component_gain(d,M,B,width=4):
    """Positive component trade or exact absence (all zero points feasible)."""
    if not M:return None,True
    basis,parts=split(d,tuple(sorted(M)),B);complete=True
    for I,F in parts:
        normals=[basis[i] for i in I]
        N={A:M[((lift(0,normals,A[0][0]),1),)] for A in F}
        assert point(N,0)==0
        y=None
        for j in range(len(I)):
            B.pay('basis_probe',1+len(N))
            if point(N,1<<j)>0:y=1<<j;break
        if y is None:
            q=positive_point(len(I),N,(),B)
            if q is not None:y=q[0]
        if y is None:
            q=moment_point(len(I),N,(),B,width=256,degree=2)
            if q is not None:y=q[0]
        if y is None:
            a,exact,t=minimum({A:-w for A,w in N.items()},len(I),B,width,with_witness=True)
            if exact and a<0:y=t
            elif a>=0:continue
            else:complete=False;continue
        z=sum(((y>>j)&1)<<i for j,i in enumerate(I));v=reopen(d,basis,z)
        assert point(M,v)==point(N,y)>0
        B.pay('gain_admit');return v,False
    return None,complete


def improve(n,P,x,B,width=4):
    v,U,K,V=quotient(n,P,x,B)
    if v is not None:return v,False
    M=gain_chart(n,x,V,B);y,done=component_gain(len(V),M,B,width)
    return (None if y is None else lift(0,V,y)),done


def solve(m,sets,cap,width=4,indexed=False,history=None,demand=False,core_trials=0,core_cover=0,core_pairs=0,hull_rows=0,lookahead_depth=0,lookahead_rounds=1,character_degree=-1,character_quotient_cap=0,character_path_steps=0,character_section_cap=0,character_adaptive_nodes=0,character_adaptive_degree=0,character_adaptive_provenance=False,exchange_rank=-1,exchange_probe_cap=1000000,exchange_small=5,exchange_rado=False,exchange_tagged=False,exchange_history=None,exchange_strata_rank=-1):
    R=incidence(m,sets);n=len(sets);B=Budget(cap);k=m//3
    try:
        B.pay('input',1+m+3*n);pins=capacity(n,R,k,B)
        if pins is None:return None,B.stats,True
        A=Matrix(m,n,lambda i,j:(R[i]>>j)&1);b=ones(m,1)
        D=integer_image(A,b,B)
        if D is None:return None,B.stats,True
        P,x=close(n,R,B,required=D+pins)
        if P is None or x is not None:return x,B.stats,True
        # Original absolute-coordinate lookahead; K refinement is independent
        # of subsequent incumbent time. Keep the existing default unchanged.
        refinement=0
        if lookahead_depth:
            from check_pnp_exact_cover_pair_hull import disjunctive_hull
            F=tuple(tuple((1<<j,0) for j in bits(a)) for a in R)
            Q,y=disjunctive_hull(n,F,B,P,lookahead_depth,lookahead_rounds)
            if Q is None or y is not None:
                if y is not None:assert satisfies(y,P,()) and cover(R,y)
                return y,B.stats,True
            refinement=int(Q!=P);P=Q
        # Reuse the character pass before gain descent; actual rank refinement
        # changes K, not the subsequent incumbent time.
        if character_degree>=0:
            from check_pnp_character_ideal import demand_character_close
            F=tuple(tuple((1<<j,0) for j in bits(a)) for a in R)
            Q,y=demand_character_close(n,F,P,B,degree=character_degree,quotient_cap=character_quotient_cap,path_steps=character_path_steps,section_cap=character_section_cap,adaptive_nodes=character_adaptive_nodes,adaptive_degree=character_adaptive_degree,adaptive_provenance=character_adaptive_provenance)
            if Q is None:return None,B.stats,True
            B.pay('character_source_rank',len(Q)-len(P))
            if y is not None:
                assert satisfies(y,Q,()) and cover(R,y)
                return y,B.stats,True
            if Q!=P:
                # Global algebraic pins are a real K refinement; feed them
                # through the existing exact-one closure before gain descent.
                Q,y=close(n,R,B,required=Q)
                if Q is None or y is not None:
                    if y is not None:assert satisfies(y,P,()) and cover(R,y)
                    return y,B.stats,True
                refinement+=1
            P=Q
            y=chart(n,P)[0];B.pay('character_source_witness_check',1+sum(a.bit_count() for a in R))
            if cover(R,y):return y,B.stats,True
            character_degree=-1 # same source/demand already observed
        x=chart(n,P)[0]
        if exchange_strata_rank>=0:
            from check_pnp_shared_row_strata import descent as strata_descent
            result=strata_descent(n,R,P,x,B,exchange_strata_rank,exchange_history,refinement)
            if result is not None:
                y,done=result
                if y is not None:assert satisfies(y,P,()) and cover(R,y)
                return y,B.stats,done
        if exchange_rank>=0:
            from check_pnp_rooted_exchange import descent
            y,done=descent(n,R,P,x,B,exchange_rank,exchange_probe_cap,exchange_small,exchange_rado,exchange_tagged,exchange_history,refinement)
            if y is not None:assert satisfies(y,P,()) and cover(R,y)
            return y,B.stats,done
        if indexed:
            from check_pnp_factorized_frontier import indexed_descent
            y,done=indexed_descent(n,P,x,k,B,width=width,history=history,k=refinement)
            if y is not None:assert cover(R,y)
            if done or not demand:return y,B.stats,done
            # Inconclusive indexed observation: reopen the same retained
            # source chart with the remaining shared budget.
        if demand:
            from check_pnp_normal_boundary_join import join_exact_one_demand
            u,V=chart(n,P)
            F=tuple(tuple((value(V,1<<j),u>>j&1) for j in bits(a)) for a in R)
            z,_=join_exact_one_demand(len(V),F,B,core_trials=core_trials,core_cover=core_cover,core_pairs=core_pairs,hull_rows=hull_rows,character_degree=character_degree)
            y=None if z is None else lift(u,V,z)
            if y is not None:assert satisfies(y,P,()) and cover(R,y)
            return y,B.stats,True
        while x.bit_count()>k:
            B.pay('descent');v,exact=improve(n,P,x,B,width)
            if v is None:return None,B.stats,exact
            y=x^v;assert satisfies(y,P,()) and y.bit_count()<=x.bit_count()-2
            x=y
        assert cover(R,x);return x,B.stats,True
    except (Exhausted,RecursionError):return None,B.stats,False


def test_character_source():
    from check_pnp_character_ideal import demand_refinement
    rng=Random(3627);stalled=improved=witness=rank_gain=source_points=source_covers=events=0
    for trial in range(36):
        m=18;S=[]
        for _ in range(5):
            a=list(range(m));rng.shuffle(a);S.extend(tuple(a[j:j+3]) for j in range(0,m,3))
        for _ in range(20):
            i,j=rng.sample(range(6,len(S)),2);a,b=rng.choice(S[i]),rng.choice(S[j])
            if a not in S[j] and b not in S[i]:
                S[i]=tuple(b if t==a else t for t in S[i])
                S[j]=tuple(a if t==b else t for t in S[j])
        planted=set(map(frozenset,S[:6]));rng.shuffle(S);n=len(S);R=incidence(m,S);seed=0
        for T in planted:seed|=1<<next(j for j,s in enumerate(S) if frozenset(s)==T)
        assert cover(R,seed)
        P,x=close(n,R,Budget(5000000));assert P is not None
        if x is not None:continue
        stalled+=1
        F=tuple(tuple((1<<j,0) for j in bits(r)) for r in R);B=Budget(5000000)
        Q=demand_refinement(n,F,P,B,degree=1);assert Q is not None and satisfies(seed,Q,())
        u,V=chart(n,canon((r,1) for r in R))
        for z in range(1<<len(V)):
            a=lift(u,V,z);source_points+=1
            if cover(R,a):assert satisfies(a,Q,());source_covers+=1
        events+=sum(B.stats.values());rank_gain+=len(Q)-len(P)
        improved+=len(Q)>len(P);witness+=cover(R,chart(n,Q)[0])
        if trial==0:
            y,stats,done=solve(m,S,5000000,indexed=True,demand=True,character_degree=1)
            assert done and y is not None and cover(R,y) and stats['character_source_rank']>0
    assert stalled==improved==witness==20
    print('character_source',36,stalled,improved,witness,rank_gain,source_points,source_covers,events)


def main():
    test_character_source()
    S=[(6,9,17),(2,9,13),(2,14,16),(0,5,15),(3,6,13),(1,13,15),(10,13,17),(0,4,8),(6,12,17),(3,8,12),(0,5,16),(4,7,9),(7,11,14),(10,12,17),(0,5,17),(1,3,4),(5,9,16),(6,10,16),(7,10,11),(1,2,13),(1,7,12),(4,7,15),(8,11,14),(1,8,14),(3,4,15),(5,10,11),(2,11,15),(2,9,12),(6,8,14),(0,3,16)]
    y,B,done=solve(18,S,20000000,indexed=True,demand=True,character_degree=1,character_quotient_cap=64)
    assert done and y is not None and cover(incidence(18,S),y)
    assert B['character_module_dimension']==4
    y,B,done=solve(18,S,20000000,indexed=True,demand=True,character_degree=1,character_path_steps=30)
    assert done and y is not None and cover(incidence(18,S),y)
    assert B['character_path_verify']>0 and not B['character_module_dimension']
    y,B,done=solve(18,S,20000000,indexed=True,demand=True,character_degree=1,character_section_cap=2,character_path_steps=30)
    assert done and y is not None and cover(incidence(18,S),y)
    y,B,done=solve(18,S,20000000,indexed=True,demand=True,character_degree=1,character_adaptive_nodes=16)
    assert done and y is not None and cover(incidence(18,S),y) and B['character_adaptive_verify']>0
    assert not solve(18,S,0,character_degree=1,character_quotient_cap=64)[2]
    rng=Random(369);fixtures=verified=empty=unknown=trades=compares=0
    for m in (3,6,9,12):
        for _ in range(70):
            n=rng.randrange(1,12);S=[tuple(rng.sample(range(m),3)) for j in range(n)];R=incidence(m,S)
            T=[x for x in range(1<<n) if cover(R,x)]
            P=canon((a,1) for a in R)
            if P is not None:
                u,W=chart(n,P);Y=[lift(u,W,j) for j in range(1<<len(W))]
                for x in Y[:8]:
                    B=Budget(1000000);v,U,K,V=quotient(n,P,x,B)
                    if v is None:
                        assert {lift(0,V,j)^x for j in range(1<<len(V))}==set(Y);compares+=1
                    v,done=improve(n,P,x,B,width=n)
                    want=any(y.bit_count()<x.bit_count() for y in Y)
                    assert (v is not None)==want and (v is not None or done)
                    if v is not None:assert x^v in Y and (x^v).bit_count()<x.bit_count();trades+=1
            y,_,finished=solve(m,S,2000000,demand=True)
            assert finished and (y is not None)==bool(T) and (y is None or y in T)
            y,_,finished=solve(m,S,2000000,demand=True,core_cover=8)
            assert finished and (y is not None)==bool(T) and (y is None or y in T)
            y,_,finished=solve(m,S,2000000,demand=True,lookahead_depth=1)
            assert finished and (y is not None)==bool(T) and (y is None or y in T)
            x,_,done=solve(m,S,2000000);fixtures+=1
            if x is not None:assert done and x in T;verified+=1
            elif done:assert not T;empty+=1
            else:unknown+=1
    # Tight hitting cover forces a genuine original column to zero.
    S=[(0,1,2),(3,4,5),(3,4,2),(2,1,4),(5,0,2),(4,3,0)]
    R=incidence(6,S);P=capacity(len(S),R,2,Budget(10000));assert P==((4,0),)
    assert all(satisfies(x,P,()) for x in range(64) if cover(R,x))
    # The old global single-normal probe can miss a positive component.
    for d in (8,16,32,64,128):
        A=[((1<<d)-1)^(1<<i) for i in range(d)]
        M={((A[0],1),):2,((A[1],1),):2,((A[0]^A[1],1),):-3}
        M.update({((a,1),):-10 for a in A[2:]})
        B=Budget(1000000);assert positive_point(d,M,(),B) is None
        C=Budget(1000000);y,done=component_gain(d,M,C)
        assert y is not None and point(M,y)==4
        print('dense_component',d,'global_probe',sum(B.stats.values()),'component',sum(C.stats.values()))
    # Independent integer-image comparison using 2L membership.
    image_checks=0
    for _ in range(160):
        m=rng.randrange(1,5);n=rng.randrange(1,7)
        A=Matrix(m,n,lambda i,j:rng.randrange(-3,4));b=Matrix(m,1,lambda i,j:rng.randrange(-3,4))
        H=hermite_normal_form(2*A);I=list(H.T.rref()[1]);D=H[I,:].inv() if H.cols else None
        P=integer_image(A,b,Budget(1000000))
        for x in range(1<<n):
            q=b-A*Matrix([x>>i&1 for i in range(n)])
            if D is None:want=not any(q)
            else:
                t=D*q[I,:];want=H*t==q and all(a.q==1 for a in t)
            assert (P is not None and satisfies(x,P,()))==want;image_checks+=1
    assert integer_image(Matrix([[3]]),Matrix([1]),Budget(1000)) is None
    print('integer_image',160,image_checks)
    # Basis trap from direct roadmap, original incumbent, not pre-solved cover.
    S=[(2,3,4),(3,4,5),(3,6,7),(3,5,8),(1,5,7),(1,4,7),(3,5,7),(0,1,2),(2,3,7),(0,4,7),(6,7,8),(3,5,6)]
    R=incidence(9,S);P=canon((a,1) for a in R);x=2840;B=Budget(1000000)
    v,done=improve(12,P,x,B);assert v is not None and cover(R,x^v)
    print('basis_trap',x^v,sum(B.stats.values()))
    # Exact all-parity-capacity counterexample from current direct roadmap.
    S=[(5,13,17),(5,14,16),(3,10,17),(0,2,16),(3,4,16),(1,10,12),(0,7,15),(6,7,10),(1,12,13),(4,5,13),(1,3,12),(0,4,6),(8,10,17),(3,7,9),(1,14,15),(9,12,15),(2,13,16),(2,12,17),(2,5,15),(6,7,8),(6,7,14),(8,11,17),(4,11,15),(5,8,11),(2,3,9),(6,9,13),(9,10,11),(0,1,16),(0,4,14),(8,11,14)]
    x,B,done=solve(18,S,10000000,width=12);assert x is None and done
    print('all_parity_barrier',sum(B.values()),'descent',B['descent'])
    assert not solve(3,[(0,1,2)],0)[2]
    print(dict(fixtures=fixtures,verified=verified,empty=empty,unknown=unknown,quotient_comparisons=compares,trades=trades))

if __name__=='__main__':main()
