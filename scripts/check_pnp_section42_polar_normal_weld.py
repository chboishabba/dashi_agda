#!/usr/bin/env python3
"""Section 42 polar-to-normal-space adapter; preserves nonlinear ANF residuals."""
import random, json
from check_pnp_affine_normal_components import Budget, split
from check_pnp_normal_boundary_join import span, intersection
from check_pnp_normal_transversal import transversal
from check_pnp_collective_fibre_escape import certificate, reopen_block

def transpose(A,n):
    return tuple(sum(((A[i]>>j)&1)<<i for i in range(n)) for j in range(n))

def mm(A,B,n):
    out=[]
    for row in A:
        z=0
        while row:
            bit=row&-row; z^=B[bit.bit_length()-1]; row^=bit
        out.append(z)
    return tuple(out)

def mv(A,x,n):
    return sum(((row&x).bit_count()&1)<<i for i,row in enumerate(A))

def bt_apply(B,x,n):
    return mv(transpose(B,n),x,n)

def inv(A,n):
    rows=[A[i] | (1<<(n+i)) for i in range(n)]
    for col in range(n):
        pivot=next((r for r in range(col,n) if (rows[r]>>col)&1),None)
        if pivot is None: raise ValueError("singular chart")
        rows[col],rows[pivot]=rows[pivot],rows[col]
        for r in range(n):
            if r!=col and ((rows[r]>>col)&1): rows[r]^=rows[col]
    return tuple((rows[i]>>n)&((1<<n)-1) for i in range(n))

def polar(planes,n):
    M=[0]*n
    for u,v in planes:
        for i in range(n):
            if (u>>i)&1: M[i]^=v
            if (v>>i)&1: M[i]^=u
    return tuple(M)

def qeval(M,l,c,x,n):
    z=c^((l&x).bit_count()&1)
    for i in range(n):
        if not ((x>>i)&1): continue
        for j in range(i+1,n):
            if ((M[i]>>j)&1) and ((x>>j)&1): z^=1
    return z

def transform_linear(M,l,c,B,n):
    # Canonical squarefree ANF gains a linear correction from x_i^2=x_i.
    columns=transpose(B,n)
    return sum((qeval(M,l,c,columns[j],n)^c)<<j for j in range(n))

def restrict_q(M,l,c,u,V,n):
    d=len(V); Mt=[0]*d
    ct=qeval(M,l,c,u,n); lt=0
    shifted=[]
    for i,v in enumerate(V):
        x=u^v; shifted.append(x)
        if qeval(M,l,c,x,n)^ct: lt|=1<<i
    for i in range(d):
        for j in range(i+1,d):
            x=shifted[i]^V[j]
            coefficient=qeval(M,l,c,x,n)^qeval(M,l,c,shifted[i],n)^qeval(M,l,c,shifted[j],n)^ct
            if coefficient: Mt[i]|=1<<j; Mt[j]|=1<<i
    return tuple(Mt),lt,ct

def small_eval(M,l,c,x,d):
    return qeval(M,l,c,x,d)

def cycle_source(n):
    if n<8 or n%2: raise ValueError("ambient n must be even and >=8")
    m=n//2; edges=[]; spaces={v:[] for v in range(m)}; E={}
    for i in range(m):
        j=(i+1)%m; P=(1<<(2*i),1<<(2*i+1))
        edges.append((i,j,P)); spaces[i].extend(P); spaces[j].extend(P); E[(i,j)]=span(P)
    return {v:span(rows) for v,rows in spaces.items()},E,edges

def dense_matrix(n,rng):
    while True:
        B=tuple(rng.getrandbits(n) for _ in range(n))
        try: inv(B,n); return B
        except ValueError: pass

def audit_cycle(n,seed):
    U,E,edges=cycle_source(n); rng=random.Random(seed); B=dense_matrix(n,rng); Bi=inv(B,n); Bt=transpose(B,n)
    payload={}; original={}
    for v in U:
        Ps=[P for a,b,P in edges if v in (a,b)]
        M=polar(Ps,n); l=rng.getrandbits(n); c=1
        Mp=mm(mm(Bt,M,n),B,n); lp=transform_linear(M,l,c,B,n)
        payload[v]=(Mp,lp,c); original[v]=(M,l,c)
        for _ in range(4):
            x=rng.getrandbits(n)
            if qeval(Mp,lp,c,x,n)!=qeval(M,l,c,mv(B,x,n),n):
                raise AssertionError("full affine/quadratic payload changed under B")
    observed={v:span(M) for v,(M,l,c) in payload.items()}
    expected={k:span(bt_apply(B,x,n) for x in P) for k,P in E.items()}
    for i in sorted(U):
        for j in range(i+1,len(U)):
            got=intersection(n,observed[i],observed[j])
            want=expected.get((i,j),expected.get((j,i),()))
            if not same_space(got,want): raise AssertionError((n,i,j,got,want))
    direct_rank=rank_all([x for _,_,P in edges for x in P],n)
    direct_dimension=sum(len(P) for _,_,P in edges)
    if direct_rank!=direct_dimension: raise AssertionError("cycle direct-sum promise failed")
    affine_count=nonlinear_count=whole_count=no_event_count=0
    affine_only_witnesses=0
    affine_correction_bits=0
    for M,l,c in original.values():
        lp=transform_linear(M,l,c,B,n)
        affine_correction_bits+=(lp^bt_apply(B,l,n)).bit_count()
    max_components=0; max_transversal=0; max_core=0
    affine_escape_witnesses=full_source_witnesses=0; restriction_checks=0
    for e,(a,b,P) in enumerate(edges):
        BiT=transpose(Bi,n)
        V=tuple(BiT[col] for col in (2*e,2*e+1))
        F=[]; residual=[]; affine_rows=[]; restricted_payloads=[]; edge_whole=0
        for v,(M,l,c) in payload.items():
            Mt,lt,ct=restrict_q(M,l,c,0,V,n)
            for t in range(4):
                x=0
                for j,w in enumerate(V):
                    if (t>>j)&1: x^=w
                if qeval(M,l,c,x,n)!=small_eval(Mt,lt,ct,t,2):
                    raise AssertionError("restricted quadratic payload changed")
                restriction_checks+=1
            restricted_payloads.append((Mt,lt,ct))
            if any(Mt):
                residual.append({"observation":v,"polar":Mt,"linear":lt,"constant":ct})
                nonlinear_count+=1
            elif lt:
                F.append(((lt,ct),)); affine_rows.append((lt,ct)); affine_count+=1
            elif ct==0:
                whole_count+=1; edge_whole+=1
            else:
                no_event_count+=1
        if F:
            _,parts=split(2,F,Budget(1000000))
            chosen,core=transversal(F,Budget(1000000))
            max_components=max(max_components,len(parts))
            max_transversal=max(max_transversal,len(chosen))
            max_core=max(max_core,len(core))
            # The collective-fibre receiver sees only the affine subset.
            # Any nonlinear residual remains attached and is not silently dropped.
            if edge_whole==0:
                cert=certificate(2,F,(1,2),Budget(1000000))
                if cert is not None:
                    _,receipt=cert
                    t=reopen_block(receipt,0,Budget(1000000))
                    if any(((a&t).bit_count()&1)==b for a,b in affine_rows):
                        raise AssertionError("affine-only reopened point lies in a forbidden flat")
                    affine_escape_witnesses+=1
                    if all(small_eval(Mt,lt,ct,t,2)==1 for Mt,lt,ct in restricted_payloads):
                        x=0
                        for j,w in enumerate(V):
                            if (t>>j)&1: x^=w
                        z=mv(B,x,n)
                        if all(qeval(M,l,c,z,n)==1 for M,l,c in original.values()):
                            full_source_witnesses+=1
                        else:
                            affine_only_witnesses+=1
    return {
        "n":n,"seed":seed,"direct_sum_rank":direct_rank,"direct_sum_dimension":direct_dimension,
        "dense_entry_fraction":sum(x.bit_count() for x in B)/(n*n),
        "all_pairwise_polar_intersections":True,
        "affine_restrictions":affine_count,"nonlinear_residuals_retained":nonlinear_count,
        "boolean_diagonal_linear_correction_bits":affine_correction_bits,
        "whole_fibre_forbidden":whole_count,"no_event_restrictions":no_event_count,
        "max_affine_components":max_components,"max_rado_transversal":max_transversal,
        "max_rado_deficient_core":max_core,"affine_escape_witnesses":affine_escape_witnesses,
        "full_original_source_witnesses":full_source_witnesses,
        "affine_only_witnesses_not_promoted":affine_only_witnesses,
        "exact_restriction_checks":restriction_checks,
        "claim_boundary":"affine receivers see only affine restrictions; nonlinear ANFs remain source-attached"
    }

def rank_all(rows,n):
    return len(span(rows))

def same_space(A,C):
    return len(span(A))==len(span(C))==len(span(tuple(A)+tuple(C)))

def overlap_triangle():
    E=[(1,2),(2,4),(4,1)]
    U=[span(E[0]+E[2]),span(E[0]+E[1]),span(E[1]+E[2])]
    dims=[len(intersection(3,U[i],U[(i+1)%3])) for i in range(3)]
    r=rank_all([x for P in E for x in P],3); d=sum(len(P) for P in E)
    if (r,d,dims)!=(3,6,[3,3,3]): raise AssertionError((r,d,dims))
    F=[tuple((a,0) for a in W) for W in U]
    chosen,core=transversal(F,Budget(100000))
    return {"status":"OVERLAP_LATTICE_REQUIRED","summand_rank":r,"summand_dimension":d,
            "pair_intersection_dimensions":dims,"rado_chosen":len(chosen),"rado_core":len(core)}

def main():
    runs=[audit_cycle(n,20261129+n) for n in (36,48,72,96)]
    overlap=overlap_triangle()
    print(json.dumps({"dense_cycle_runs":runs,"overlap_triangle":overlap,"status":"PASS",
           "claim_ceiling":"finite polar/affine adapter only; not a quadratic SAT producer or Clay endpoint"},indent=2,sort_keys=True))

if __name__=="__main__": main()
