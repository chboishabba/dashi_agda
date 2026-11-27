"""Scoped forbidden-flat masked minima and simultaneous capacity reopening.

Reuse the normal-boundary tree. Completed tables are exact; width refusal is
UNKNOWN. No truth oracle, ambient enumeration, or independent-row witness merge.
All Walsh coefficients, including the zero mode, are doubled integer weights.
"""
from check_pnp_affine_normal_components import canon, chart, lift, restrict, satisfies
from check_pnp_normal_boundary_join import tree, rows, value
from check_pnp_signed_capacity_square import row_ledger, evaluate
from check_pnp_signed_capacity_implication import screen as implication


def fold(n, factors, B, width=6, audit=None):
    """Each factor is (normal support, local cost or None for forbidden).
    Return (completed, minimum or None, witness or None, observed width).
    One attaining receipt per boundary label suffices by the normal-space
    intersection property of tree; no optimal width claim.
    """
    B.pay('masked_input',1+n+sum(1+len(A) for A,_ in factors))
    if not factors:return True,0,0,0
    F=tuple(tuple((a,0) for a in A) for A,_ in factors)
    root,boundary,space=tree(n,F,B)
    peak=0
    def run(node):
        nonlocal peak
        mask,L,R=node;D=boundary(mask);U=space(mask)
        peak=max(peak,len(D))
        if len(D)>width:return None
        T={}
        if L is None:
            peak=max(peak,len(U))
            if len(U)>width:return None
            _,cost=factors[mask.bit_length()-1]
            B.pay('masked_leaf', (1<<len(U))*(1+n+len(U)+len(D)))
            for v in range(1<<len(U)):
                H=rows(U,v);x=chart(n,canon(H))[0];c=cost(x)
                if c is None:continue
                p=value(D,x)
                if p not in T or c<T[p][0]:T[p]=(c,H)
        else:
            A=run(L)
            if A is None:return None
            C=run(R)
            if C is None:return None
            B.pay('masked_join',1+len(A)*len(C)*(1+n)**2)
            for a,H in A.values():
                for b,K in C.values():
                    J=canon(H+K)
                    if J is None:continue
                    p=value(D,chart(n,J)[0]);c=a+b
                    if p not in T or c<T[p][0]:T[p]=(c,J)
        B.pay('masked_table',1+len(T)*(1+len(U)))
        if audit is not None:audit.append(dict(mask=mask,boundary=D,space=U,table=tuple(sorted(T.items()))))
        return T
    T=run(root)
    if T is None:return False,None,None,peak
    if not T:return True,None,None,peak
    c,H=T[0];x=chart(n,canon(H))[0]
    assert all(f(x) is not None for _,f in factors)
    assert sum(f(x) for _,f in factors)==c
    return True,c,x,peak


def flat_factors(F):
    return [(tuple(a for a,b in G),lambda x,G=G:0 if satisfies(x,(),(G,)) else None) for G in F]


def masked_minimum(n,M,F,B,width=6,audit=None):
    """Exact minimum of doubled signed row ledger on the allowed carrier."""
    B.pay('masked_modes',1+len(M))
    factors=flat_factors(F)
    factors.extend(((a,),lambda x,a=a,c=c:-c if (a&x).bit_count()%2 else c)
                   for a,c in sorted(M.items()) if a and c)
    done,c,x,w=fold(n,factors,B,width,audit)
    if c is not None:c+=M.get(0,0)
    if x is not None:assert satisfies(x,(),F) and evaluate(M,x)==c
    return done,c,x,w


def capacity_join(n,M,caps,F,B,width=6,audit=None):
    """Simultaneous original row constraints, not separate row minimizers."""
    assert len(M)==len(caps)
    B.pay('masked_capacity_input',1+sum(1+len(m) for m in M))
    factors=flat_factors(F)
    for m,c in zip(M,caps):
        A=tuple(sorted(a for a,k in m.items() if a and k))
        factors.append((A,lambda x,m=m,c=c:0 if evaluate(m,x)<=2*c else None))
    done,_,x,w=fold(n,factors,B,width,audit)
    if x is not None:
        assert satisfies(x,(),F) and all(evaluate(m,x)<=2*c for m,c in zip(M,caps))
    return done,x,w


def screen(n,R,H,caps,B,width=6,audit=None):
    """Run implication closure, then consume its verified original-scope flats.
    Return the same triple as implication.screen. Refusal retains the refined
    carrier. Budget exhaustion is handled by the existing outer consumer.
    """
    obs=[]
    K,y,why=implication(n,R,H,caps,B,audit=obs)
    if audit is not None:audit.extend(obs)
    if K is None or y is not None or why!='imp_stalled':return K,y,why
    F0=obs[-1]['retained_original_flats']
    B.pay('masked_scope',1+(n+1)*(1+len(K)+sum(1+len(G) for G in F0)))
    u,V,F=restrict(n,K,F0,B)
    d=len(V)
    B.pay('masked_group',1+sum(r.bit_count() for r in R)*(1+d))
    M=[row_ledger(r,u,V) for r in R]
    for i,(m,c) in enumerate(zip(M,caps)):
        trace=[] if audit is not None else None
        done,lo,z,w=masked_minimum(d,m,F,B,width,trace)
        if audit is not None:audit.append(dict(kind='masked_minimum',scope=K,row=i,done=done,minimum=lo,width=w,tables=trace))
        if done and (lo is None or lo>2*c):return None,None,'masked_empty'
    trace=[] if audit is not None else None
    done,z,w=capacity_join(d,M,caps,F,B,width,trace)
    if audit is not None:audit.append(dict(kind='masked_joint',scope=K,done=done,witness=z,width=w,tables=trace))
    if not done:return K,None,'masked_width_refusal'
    if z is None:return None,None,'masked_joint_empty'
    y=lift(u,V,z)
    B.pay('masked_original_verify',1+n+sum(r.bit_count() for r in R))
    assert satisfies(y,K,F0) and all((r&y).bit_count()<=c and (r&y).bit_count()%2==1 for r,c in zip(R,caps))
    return K,y,'masked_joint_witness'
