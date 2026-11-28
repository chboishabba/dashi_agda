"""Leech lattice mod 2 / Weyl BIDI and selected M2 flavour tensors.
Classical Golay construction; no assertion of canonical FLM lift or VOA modes.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
import numpy as np
import sympy as s
from sympy.matrices.normalforms import hermite_normal_form

N=24
I=np.eye(N,dtype=np.int64)

def lattice():
    # Extended cyclic binary Golay [23,12,7], parity at coordinate 23.
    g=sum(1<<i for i in (0,1,5,6,7,9,11))
    gen=[(g<<i)|(((g<<i).bit_count()%2)<<23) for i in range(12)]
    code=[0]
    for v in gen: code += [x^v for x in code]
    assert len(set(code))==4096
    assert Counter(x.bit_count() for x in code)=={0:1,8:759,12:2576,16:759,24:1}
    C=np.array([[(v>>i)&1 for i in range(N)] for v in gen],dtype=np.int64)
    assert not np.any(C@C.T%2)
    # Even sublattice: 2c+4z, c in Golay, sum(z) even; add odd glue.
    odd=np.ones(N,dtype=np.int64);odd[0]=-3
    B=hermite_normal_form(s.Matrix(np.vstack([2*C,4*(I[1:]-I[0]),8*I[0:1],odd[None,:]]).T.tolist()))
    assert abs(B.det())==2**36
    G=B.T*B/8
    assert G.det()==1 and all(v.q==1 for v in G) and all(G[i,i]%2==0 for i in range(N))
    # Rootlessness: even norm-2 requires one +/-4, excluded by sum mod8,
    # or four +/-2, excluded by Golay weight; odd vectors norm >=24/8.
    # The three norm-4 families: two +/-4; octad +/-2 with even minus;
    # one +/-3 and 23 +/-1, with sign word determined by Golay code.
    counts=(4*276,759*128,24*4096)
    assert sum(counts)==196560
    return B,G,C,code,counts

def minimal(B,G,code):
    # All three literal norm-four families, antipodal pairs in Lambda/2Lambda.
    rows=[]
    for i,j in combinations(range(N),2):
        for a,b in product((-4,4),repeat=2):
            x=np.zeros(N,dtype=np.int64);x[i]=a;x[j]=b;rows.append(x)
    for word in code:
        if word.bit_count()!=8:continue
        ids=[i for i in range(N) if word>>i&1]
        for bits in range(256):
            if bits.bit_count()%2:continue
            x=np.zeros(N,dtype=np.int64);x[ids]=[2-4*(bits>>j&1) for j in range(8)];rows.append(x)
    signs=np.array([[1-2*(word>>i&1) for i in range(N)] for word in code])
    for i in range(N):
        x=np.ones(N,dtype=np.int64);x[i]=-3;rows.extend(signs*x)
    X=np.array(rows);assert len(X)==196560 and np.all(np.sum(X*X,axis=1)==32)
    assert len(np.unique(X,axis=0))==len(X)
    inv=B.inv(); d=int(s.ilcm(*[x.q for x in inv])); A=np.array((d*inv).tolist(),dtype=np.int64)
    coords=X@A.T;assert not np.any(coords%d); coords=coords//d%2
    labels=coords@(1<<np.arange(N)); keys,counts=np.unique(labels,return_counts=True)
    assert len(keys)==98280 and keys[0]>0 and np.all(counts==2)
    assert np.all(np.einsum('bi,ij,bj->b',coords,np.array(G.tolist(),dtype=np.int64),coords)%4==0)
    print('literal norm-four vectors',len(X),'distinct antipodal mod2 classes',len(keys),flush=True)

def mod2(G):
    G=np.array(G.tolist(),dtype=np.int64); Q=np.diag(G)//2%2
    U=(np.triu(G,1)+np.diag(Q))%2
    q=lambda x:int(x@U@x%2)
    b=lambda x,y:int(x@G@y%2)
    # Choose hyperbolic pairs; project remaining basis onto complement.
    pool=list(I.copy()); E=[]; F=[]
    while pool:
        e=next((x for x in pool if q(x)==0),None)
        if e is None:e=next((x^y for x,y in combinations(pool,2) if q(x^y)==0),None)
        assert e is not None
        f=next(x.copy() for x in pool if b(e,x))
        f^=q(f)*e
        assert q(e)==q(f)==0 and b(e,f)==1
        E.append(e);F.append(f)
        # retain independent projected columns by binary elimination
        piv={};new=[]
        for x in pool:
            z=x^(b(x,f)*e)^(b(x,e)*f); w=z.copy()
            for i in range(N):
                if w[i]:
                    if i in piv:w^=piv[i]
                    else:piv[i]=w;new.append(z);break
        assert len(new)==len(pool)-2
        pool=new
    P=np.stack(E+F,axis=1)
    J=np.block([[np.zeros((12,12),int),np.eye(12,dtype=int)],[np.eye(12,dtype=int),np.zeros((12,12),int)]])
    assert np.array_equal(P.T@G@P%2,J)
    # inverse of the chart: J P^T G; preserve all 24 coordinates.
    Pinv=J@P.T@G%2
    assert np.array_equal(P@Pinv%2,I) and np.array_equal(Pinv@P%2,I)
    # Cocycle of T_a M_b is b dot a'. Difference of two cocycles
    # is symmetric with zero diagonal, hence a quadratic coboundary.
    V=np.tril(J,-1); D=(P.T@U@P+V)%2
    assert np.array_equal(D,D.T) and not np.any(np.diag(D))
    K=np.triu(D,1); phase=lambda x:int(x@K@x%2)
    rng=np.random.default_rng(369)
    for x,y in list(product(I,I))+[(rng.integers(0,2,N),rng.integers(0,2,N)) for _ in range(4096)]:
        assert int(x@D@y%2)==(phase(x)^phase(y)^phase(x^y))
    print('Leech Gram det=1, hyperbolic pairs=12, Arf=0, cocycle BIDI 4672 controls',flush=True)
    return U,P,Pinv

def lift(B,G,C,U):
    # Actual octad sign-change automorphism of the lattice (not an arbitrary
    # symplectic automorphism). Compute an explicit lift in original basis.
    c=next(v for v in C if sum(v)==8)
    A=B.inv()*s.diag(*[1-2*int(x) for x in c])*B
    assert all(x.q==1 for x in A) and A*A==s.eye(N) and A.T*G*A==G
    A=np.array(A.tolist(),dtype=np.int64)%2
    D=(A.T@U@A+U)%2
    assert np.array_equal(D,D.T) and not np.any(np.diag(D))
    K=np.triu(D,1); f=lambda x:int(x@K@x%2)
    square=np.array([f(x)^f(A@x%2) for x in I])
    # Squared lift central character; do not identify with canonical FLM lift.
    for x,y in product(I,I):
        assert (f(x)^f(y)^f(x^y))==int(x@D@y%2)
    assert np.array_equal(A@A%2,I)
    # Solve (A+I)^T l=square over F2, so the rephased lift squares to one.
    mat=np.column_stack(((A+I).T%2,square)); piv=[];row=0
    for col in range(N):
        k=next((k for k in range(row,N) if mat[k,col]),None)
        if k is None:continue
        mat[[row,k]]=mat[[k,row]]
        for j in range(N):
            if j!=row and mat[j,col]:mat[j]^=mat[row]
        piv.append(col);row+=1
    assert not np.any(mat[row:,-1]); l=np.zeros(N,dtype=np.int64);l[piv]=mat[:row,-1]
    assert np.array_equal((A+I).T@l%2,square)
    f2=lambda x:f(x)^int(l@x%2)
    assert all(f2(x)==f2(A@x%2) for x in I)
    print('actual octad automorphism, lift-square character weight',sum(square),'corrected involution PASS',flush=True)

def action():
    # Published Eq75 tensor spaces: A, B, C, D, E, F, G, H.
    # In eigenbasis exchange splits 2=1+1 and 6=3+3.
    sig2=[1,-1];sig6=[1]*3+[-1]*3
    sym=lambda sig,d:[np.prod(v) for v in combinations_with_replacement(sig,d)]
    ext=lambda sig,d:[np.prod(v) for v in combinations(sig,d)]
    # odd slots: count monomials for equivariant Hom target <- source.
    specs=[(sig2,sig6),(sig6,sym(sig2,2)),(sig6,sig6),(sig6,[x*y for x,y in product(sig2,sig6)]),(sig6,sig2),(sig2,sym(sig2,3)),(sig2,ext(sig6,2)),(sig2,[x*y for x,y in product(sig6,sig2)])]
    total=[len(a)*len(b) for a,b in specs]; keep=[sum(x==y for x,y in product(a,b)) for a,b in specs]
    assert total==[12,18,36,72,12,8,30,24] and keep==[6,9,18,36,6,4,15,12]
    assert sum(total)==212 and sum(keep)==106
    print('M2 Eq75 coefficients',total,'exchange-invariant',keep,flush=True)
    # A nonzero odd cubic coupling is allowed by the published tensor format,
    # but is not exchange equivariant. Projection gives exact repair.
    X=s.Matrix([[0,1],[1,0]]); M=s.Matrix([[1,0],[0,0]])
    assert X*M*X!=M and X*((M+X*M*X)/2)*X==(M+X*M*X)/2
    # 27D field-strength terms with nonzero linear maps can change mass spectrum.
    # No claim of gauge invariance, CS quantization or selected physical coefficients.

if __name__=='__main__':
    B,G,C,code,counts=lattice();print('Leech norm4 family counts',counts,flush=True)
    minimal(B,G,code);U,P,Pinv=mod2(G);lift(B,G,C,U);action()
