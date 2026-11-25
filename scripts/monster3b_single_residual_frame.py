"""Source-only good-prime certificate, with a characteristic-zero expression recipe.
Target matrix checks require the same marked source cover; no Monster claim.
"""
import numpy as np
from monster3b_singer_cyclic_hom import orbit, wheel, word, rank_mod, mm, ident, require, P
from monster3b_actual_projective_sym2_intertwiner import inverse
from monster3b_lindsey_actual_mod31_join import source_matrices, dual

def poly_eval(c,M):
    I=ident(len(M)); R=np.zeros_like(M)
    for a in c:R=(mm(R,M)+a*I)%P
    return R

def words_at(ops,words):
    G,_=wheel(ops,len(ops['D']))
    return np.stack([word({**ops,'G':G},w) for w in words])

def charpoly(M):
    # Similarity to upper Hessenberg, then determinant recurrence (ascending coefficients).
    H=M.copy()%P;n=len(H)
    for k in range(n-2):
        i=next((i for i in range(k+1,n) if H[i,k]),None)
        if i is None:continue
        H[[i,k+1]]=H[[k+1,i]];H[:,[i,k+1]]=H[:,[k+1,i]]
        for i in range(k+2,n):
            a=int(H[i,k])*pow(int(H[k+1,k]),-1,P)%P
            H[i]=(H[i]-a*H[k+1])%P
            H[:,k+1]=(H[:,k+1]+a*H[:,i])%P
    pol=[np.array([1],dtype=np.int64)]
    for m in range(1,n+1):
        v=np.convolve(pol[-1],[-H[m-1,m-1],1])%P;f=1
        for i in range(m-2,-1,-1):
            f=f*int(H[i+1,i])%P
            v[:i+1]=(v[:i+1]-int(H[i,m-1])*f*pol[i])%P
        pol.append(v)
    c=pol[-1][::-1].tolist()
    require(not np.any(poly_eval(c,M)),'characteristic polynomial residual')
    return c

def source_frame(ops):
    n=len(ops['D']); B,words,_=orbit(ops); A=words_at(ops,words)
    i={12:0,78:26}[n]; c=mm(inverse(B),mm(ops['D'],B))[:,i]
    R=(mm(ops['D'],A[i])-np.tensordot(c,A,axes=1))%P
    require(not np.any(R[:,0]),'source residual seed')
    require(rank_mod(R)==rank_mod(mm(R,R))==n-1,'nonsemisimple or multiple zero')
    p=charpoly(R)
    require(p[-1]==0 and p[-2]!=0,'bad source polynomial')
    p0=p[-2];p=[a*pow(p0,-1,P)%P for a in p[:-1]]
    Q=poly_eval(p,R);v=ident(n)[:,0]
    require(rank_mod(Q)==1 and np.array_equal(mm(Q,Q),Q) and np.array_equal(Q@v%P,v),'source projector')
    lam=Q[0,:];require(np.array_equal(Q,np.outer(v,lam)%P),'source line')
    H=mm(np.stack([lam@inverse(a)%P for a in A]),B); Hi=inverse(H)
    return dict(words=words,index=i,coefficients=c.tolist(),projector_poly=p,p0=p0,
                dual_pairing_inverse=Hi.tolist(),dimension=n,source_rank=n-1,
                exact_recipe='B=[A(w_i)e0]; c=B^-1 A(D)B[:,i]; R=A(D)A(w_i)-sum c_j A(w_j); p=det(tI-R)/t; Q=p(R)/p(0); lambda=e0^T Q; H_ji=lambda A(w_j)^-1 A(w_i)e0; H^-1 exact over Q(zeta). Modular coefficients are NOT exact characteristic-zero coefficients.')

def target_frame(ops,rec):
    n=rec['dimension'];A=words_at(ops,rec['words']); Ai=np.stack([inverse(a) for a in A])
    R=(mm(ops['D'],A[rec['index']])-np.tensordot(rec['coefficients'],A,axes=1))%P
    Q=poly_eval(rec['projector_poly'],R)
    require(rank_mod(Q)==1 and np.array_equal(mm(Q,Q),Q),'target seed line')
    U=np.stack([mm(Q,a) for a in np.tensordot(np.asarray(rec['dual_pairing_inverse']),Ai,axes=1)%P])
    require(np.array_equal(sum(mm(a,u) for a,u in zip(A,U))%P,ident(n)),'target completeness')
    # Rank-one factoring avoids n^2 dense matrix products; same identities.
    y=Q[:,next(j for j in range(n) if np.any(Q[:,j]))]
    pivot=next(i for i in range(n) if y[i]);lam=Q[pivot,:]*pow(int(y[pivot]),-1,P)%P
    require(np.array_equal(Q,np.outer(y,lam)%P),'target line factor')
    T=np.column_stack([a@y%P for a in A]);Ti=inverse(T)
    for i,u in enumerate(U):
        require(np.array_equal(u,np.outer(y,Ti[i,:])%P),'target dual row')
    require(np.array_equal(mm(Ti,T),ident(n)),'all dual orbit equations')
    return Q,A,U,T,Ti

def trace_vacuum(character,z,modulations,g,zeta,one,s,coefficient):
    """Exact phase-preserving Hom trace from authenticated original word traces."""
    from itertools import product
    require(s in (1,2) and coefficient!=one-one,'wrong phase or zero Weil vacuum')
    total=one-one
    for a in product(range(3),repeat=len(modulations)):
        b=z**0
        for t,k in zip(modulations,a):b=b*t**k
        for j in range(3):total+=zeta**(-s*j)*character(z**j*b*g)
    return total/(3**(len(modulations)+1)*one*coefficient)

def selftest(data):
    rng=np.random.default_rng(369);out=[]
    for q in range(3):
        T=source_matrices(data,q);U={g:dual(T[g],g=='C') for g in T}
        for n,src in ((12,T),(78,U)):
            A={g:src[g][:n,:n] for g in ('D','E')};rec=source_frame(A)
            X=(ident(n)+np.triu(rng.integers(0,P,(n,n)),1))%P;Xi=inverse(X)
            L={g:mm(mm(X,a),Xi) for g,a in A.items()}
            Q,Ts,Us,Bt,Bti=target_frame(L,rec)
            Bs,_,_=orbit(A);F=mm(Bt,inverse(Bs))
            require(all(np.array_equal(mm(F,A[g]),mm(L[g],F)) for g in A),'generator mismatch')
            a=rng.integers(0,P,n);w=Bt@a%P;ys=[u@w%P for u in Us]
            require(all(np.array_equal(Q@y%P,y) for y in ys),'line range')
            require(np.array_equal(sum(t@y%P for t,y in zip(Ts,ys))%P,w),'mixed inverse')
            out.append(dict(q=q,n=n,index=rec['index'],dual_checks=n*n,p0=rec['p0'],degree=len(rec['projector_poly'])-1))
    return out

if __name__=='__main__':
    import json
    from pathlib import Path
    data=json.loads((Path(__file__).resolve().parents[1]/'Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json').read_text())
    print(json.dumps(selftest(data),indent=2))
