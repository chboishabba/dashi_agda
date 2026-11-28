#!/usr/bin/env python3
"""BR85–88: actual geometric boundary jets, positive connection energy,
direct BR34 principal glancing inverses, and BR29 moving Weyl source.

Classical geometry/energy identities retain prior-math attribution.
DASHI contribution: direct original row inverse and source-indexed weld.
These checks are not a variable-coefficient IBVP or kernel certificate.
"""
import argparse
from itertools import combinations_with_replacement
import sympy as s

Q=s.Rational
I=s.eye(5)
Z=s.zeros
pairs=list(combinations_with_replacement(range(5),2))
def eq(a,b):
    assert a.shape==b.shape
    assert (a-b).applyfunc(s.cancel)==Z(*a.shape)
def sym(seed):
    return s.Matrix(5,5,lambda i,j:Q((min(i,j)+2)*(max(i,j)+seed+3)%17-8,19+seed))
def connection(ginv,dg):
    return [s.Matrix(5,5,lambda i,j:sum(ginv[k,l]*(dg[i][l,j]+dg[j][l,i]-dg[l][i,j]) for l in range(5))/2) for k in range(5)]
def physical_data():
    # Graph tangent with genuine time and tangential tilt; both h and g
    # non-diagonal, spacelike conormal of exact squared length one.
    f=s.Matrix([Q(1,7),Q(-2,9),Q(1,11),Q(2,13)])
    E=I[:,:4].copy(); E[4,:]=f.T
    F=s.Matrix([-x for x in f]+[1]); B=E.row_join(I[:,4])
    L=s.eye(4); L[2,0]=Q(1,5); L[3,1]=Q(-2,7)
    h=L.T*s.diag(-2,3,4,5)*L
    v=s.Matrix([Q(1,3),Q(-1,7),Q(2,9),Q(1,11)])
    G=h.row_join(h*v).col_join((v.T*h).row_join(s.Matrix([[1+(v.T*h*v)[0]]])))
    g=B.inv().T*G*B.inv(); gi=g.inv()
    assert (F.T*gi*F)[0]==1
    eq(E.T*g*E,h)
    return g,gi,E,F,h
def geom(g,gi,E,F,H,dg):
    z=(F.T*gi*F)[0]; n=gi*F/s.sqrt(z)
    Gamma=connection(gi,dg)
    A=H-sum((F[k]*Gamma[k] for k in range(5)),Z(5))
    K=E.T*A*E/s.sqrt(z)
    C=s.Matrix([sum(gi[i,j]*(dg[i][j,k]-dg[k][i,j]/2) for i in range(5) for j in range(5)) for k in range(5)])
    return E.T*g*E,K,E.T.col_join(n.T)*C,A,C,n
def br85():
    from check_hopf369_br63_nonlinear_israel_inverse import original_junction,original_inverse
    g,gi,E,F,h=physical_data()
    e=s.symbols('e',real=True)
    u=s.Matrix([Q(i-2,7) for i in range(5)]); p=u*u.T
    df=s.Matrix([Q(2-i,13) for i in range(4)]+[0])
    dE=Z(5,4); dE[4,:]=-df[:4,0].T
    H=Z(5); H[:4,:4]=sym(1)[:4,:4]
    dH=Z(5); dH[:4,:4]=sym(2)[:4,:4]
    dgi=-gi*p*gi
    dz=(2*df.T*gi*F+F.T*dgi*F)[0]
    dn=dgi*F+gi*df-dz*gi*F/2
    dh=dE.T*g*E+E.T*p*E+E.T*g*dE
    Ks=[]; dKs=[]
    for seed in (3,11):
        dg=[sym(seed+k) for k in range(5)]
        ddg=[sym(seed+k+7) for k in range(5)]
        hh,K,gauge,A,C,n=geom(g,gi,E,F,H,dg)
        Ga=connection(gi,dg); dGa0=connection(dgi,dg); dGa1=connection(gi,ddg)
        dA=dH-sum((df[k]*Ga[k]+F[k]*(dGa0[k]+dGa1[k]) for k in range(5)),Z(5))
        dK=dE.T*A*E+E.T*dA*E+E.T*A*dE-dz*K/2
        dC=s.Matrix([sum(dgi[i,j]*(dg[i][j,k]-dg[k][i,j]/2)+gi[i,j]*(ddg[i][j,k]-ddg[k][i,j]/2) for i in range(5) for j in range(5)) for k in range(5)])
        dGauge=dE.T.col_join(dn.T)*C+E.T.col_join(n.T)*dC
        # Independent exact nonlinear oracle: rank-one metric path
        # via Sherman–Morrison, not the derivative formula above.
        v=gi*u; ie=gi-e*v*v.T/(1+e*(u.T*gi*u)[0])
        ge=g+e*p; Ee=E+e*dE; Fe=F+e*df
        assert Fe.T*Ee==Z(1,4)
        # Differentiate the literal nonlinear expression componentwise
        # using its exact scalar denominator, keeping graph normalization.
        ze=s.cancel((Fe.T*ie*Fe)[0])
        Gae=connection(ie,[a+e*b for a,b in zip(dg,ddg)])
        Ae=H+e*dH-sum((Fe[k]*Gae[k] for k in range(5)),Z(5))
        num=Ee.T*Ae*Ee
        directK=num.applyfunc(lambda x:s.diff(x,e).subs(e,0))-num.subs(e,0)*s.diff(ze,e).subs(e,0)/2
        eq(directK,dK)
        eq((Ee.T*ge*Ee).diff(e).subs(e,0),dh)
        Ce=s.Matrix([sum(ie[i,j]*((dg[i]+e*ddg[i])[j,k]-(dg[k]+e*ddg[k])[i,j]/2) for i in range(5) for j in range(5)) for k in range(5)])
        tang=Ee.T*Ce
        norm=(Fe.T*ie*Ce)[0]
        directGauge=tang.diff(e).subs(e,0).col_join(s.Matrix([s.diff(norm,e).subs(e,0)-norm.subs(e,0)*s.diff(ze,e).subs(e,0)/2]))
        eq(directGauge,dGauge)
        assert dGauge!=E.T.col_join(n.T)*dC # frame derivative indispensable
        assert dK!=E.T*dA*E # graph/normal derivative indispensable
        Ks.append(K);dKs.append(dK)
    k=Ks[0]-Ks[1]; dk=dKs[0]-dKs[1]; j=Q(-6,5); dj=Q(1,17)
    hi=h.inv(); dhi=-hi*dh*hi
    tr=s.trace(hi*k); dt=s.trace(dhi*k+hi*dk)
    dIsrael=dk-dh*tr-h*dt+3*dj*h+3*j*dh
    Is=original_junction(h,k,j); src=Is-3*j*h
    dsrc=dIsrael-3*dj*h-3*j*dh
    back=dsrc-(dh*s.trace(hi*src)+h*s.trace(dhi*src+hi*dsrc))/3
    eq(back,dk);eq(original_inverse(h,Is,j),k)
    print('PASS BR85 moving two-face h/K/gauge first jets and differentiated BR63 Israel inverse; matched induced h')
    print('BR85 boundary: directional oracle; full BR71/72 row equivalence at physical solution remains open')

def induced_connection(A):
    # A acts on covectors; induce the same connection on symmetric
    # covariant 2-tensors, with all 15 packed components.
    def unpack(k):
        i,j=pairs[k]; m=Z(5);m[i,j]=m[j,i]=1;return m
    return s.Matrix.hstack(*(s.Matrix([(A*unpack(k)+unpack(k)*A.T)[i,j] for i,j in pairs]) for k in range(15)))
def br86():
    H=s.diag(2,3,4,5); L=s.eye(4);L[2,0]=Q(1,3)
    H=L.T*H*L; Hi=H.inv();N=Q(3,2);v=s.Matrix([Q(i-1,5) for i in range(4)])
    X=s.Matrix([1,*(-v)])/N
    gi=(-s.Matrix([[1/N**2]])).row_join((v/N**2).T).col_join((v/N**2).row_join(Hi-v*v.T/N**2))
    g=gi.inv()
    assert (X.T*g*X)[0]==-1
    M=gi+2*X*X.T
    # Exact positive coordinate norm from ADM normal/spatial split.
    R=s.eye(5);R[0,:]=X.T
    eq(M,R.T*s.diag(1,Hi)*R)
    basis=[]
    for i,j in pairs:
        p=Z(5);p[i,j]=p[j,i]=1;basis.append(p)
    G15=s.Matrix(15,15,lambda i,j:s.trace(M*basis[i]*M*basis[j]))
    assert G15.is_positive_definite and M.is_positive_definite
    S=s.diag(1,Hi)
    for i in range(4):
        A=Z(5);A[0,1:]=Hi[i,:];A[1:,0]=s.eye(4)[:,i]
        eq(S*A,(S*A).T)
        for G in (G15,M):
            # Kronecker principal energy on 15 and 5 channels.
            eq(s.kronecker_product(G,S*A),s.kronecker_product(G,S*A).T)
    Ga=connection(gi,[sym(i+2) for i in range(5)])
    # Covector connection along direction 0: A_i^k=-Gamma^k_{0i}.
    A5=s.Matrix(5,5,lambda i,k:-Ga[k][0,i]);A15=induced_connection(A5)
    for G,A in ((M,A5),(G15,A15)):
        n=G.rows; u=s.Matrix([Q(i+1,7) for i in range(n)])
        ud=s.Matrix([Q(i-2,11) for i in range(n)])
        Gd=G/7 # independent positive Gram first jet, not assumed zero
        work=Gd-A.T*G-G*A
        exact=(ud.T*G*u+u.T*G*ud+u.T*Gd*u)[0]
        assert exact==2*((ud+A*u).T*G*u)[0]+(u.T*work*u)[0]
        assert work!=Z(n)
        # Divided time-jet commutator through order 8, using actual
        # nonzero connection operator rather than independent channels.
        jets=[(A+Q(k,17)*s.eye(n))*Q(1,k+1) for k in range(9)]
        fields=[u*Q((-1)**k,k+2)+ud*Q(k,19) for k in range(9)]
        t=s.symbols('t')
        # Independent direct coefficient extraction on actual scalar
        # contraction of the matrix polynomial and every field channel.
        for i in range(n):
            poly=sum((jets[k]*fields[l])[i]*t**(k+l) for k in range(9) for l in range(9) if k+l<=8)
            for k in range(9):
                direct=s.expand(poly).coeff(t,k)-(jets[0]*fields[k])[i]
                assert direct==sum((jets[a]*fields[k-a])[i] for a in range(1,k+1))
    print('PASS BR86 positive 15+5 ADM fibre symmetrizers, connection work and order 0..8 exact commutators')
    print('BR86 boundary: pointwise/principal construction, not integrated Sobolev estimate or dissipative wall')

def br87(alloc,sector):
    from check_hopf369_br_warped_physical_attachment import metric_rows,gauge_rows
    from check_hopf369_br_full_warped_symbol import dec
    w=s.symbols('w',nonzero=True)
    z=s.Matrix([(w+1/w)/2,(w-1/w)/2,0,0])
    assert s.cancel((z.T*s.diag(-1,1,1,1)*z)[0]+1)==0
    n=30 if sector=='metric' else 10
    def row(v):
        if sector=='metric':
            p,m=dec(v[:15,0]),dec(v[15:,0])
            return metric_rows(p,-p,m,m,z,s.S.Zero,alloc)
        p,m=v[:5,0],v[5:,0]
        return gauge_rows(p,-p,m,m,z,s.S.Zero,alloc)
    B=s.Matrix.hstack(*(row(s.eye(n)[:,k]) for k in range(n)))
    inv=B.inv(method='DM').applyfunc(s.cancel)
    eq(B*inv,s.eye(n));eq(inv*B,s.eye(n))
    # Along sigma=1, omega>=0: w=ell, w²=1+2i omega,
    # |w|>=1, |w²+1|>=|w|². Every exact denominator is
    # constant * w^a * (w²+1)^b, so coefficient l1 gives a
    # rigorous bound by C |w|^degree, not a sample fit.
    costs=[]; degrees=[]
    for x in inv:
        if not x: costs.append(0);continue
        num,den=s.fraction(x); const,factors=s.factor_list(den,w)
        for base,power in factors:
            assert base in (w,w*w+1),(base,power)
        degree=s.degree(num,w)-s.degree(den,w)
        degrees.append(degree)
        costs.append(sum(abs(c) for c in s.Poly(num,w).all_coeffs())/abs(const))
    power=max(degrees)
    assert power=={('D','metric'):3,('D','gauge'):2,('E','metric'):1,('E','gauge'):1}[alloc,sector]
    bound=max(sum(costs[i*n:(i+1)*n]) for i in range(n))
    assert bound=={('D','metric'):19,('D','gauge'):4,('E','metric'):Q(31,4),('E','gauge'):Q(11,2)}[alloc,sector]
    # Opposite regime: sigma fixed, omega=0 and |xi| grows.
    # w=(sigma+i|xi|)/sqrt(sigma²+|xi|²) approaches i,
    # and w²+1=2w sigma/ell tends to zero. E has genuine simple
    # poles, while D has Laurent-only denominators. A sectorwise
    # comparison is not permission to switch physical boundary rows.
    residues=[s.cancel((w-s.I)*x).subs(w,s.I) for x in inv]
    count=sum(x!=0 for x in residues)
    assert count=={('D','metric'):0,('D','gauge'):0,('E','metric'):12,('E','gauge'):8}[alloc,sector]
    if alloc=='E':
        assert all(s.cancel((w-s.I)*x).subs(w,s.I).is_finite for x in inv)
        print(f'BR87 REFUSAL: {count} actual E inverse entries have a simple pole at w=i (low temporal/high spatial sector)')
    # Nonzero leading coefficient also gives the matching asymptotic
    # lower exponent for this matrix on the ray.
    lead=[s.limit(x/w**power,w,s.oo) for x in inv if x]
    assert any(x!=0 for x in lead)
    print(f'PASS BR87 {alloc}/{sector}: two-sided exact inverse, norm <= {bound} |ell|^{power}; sharp ray exponent {power}/2 in omega')
    print('BR87 boundary: normalized flat decaying principal half-space, not finite warped DtN or variable glancing')

def br88():
    from check_hopf369_br_curvature_energy import carrier,P,eta
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier()
    An=A[3]; P0=s.eye(35)-An*(5*An-4*An**3)
    assert P0.rank()==9;eq(P0*An,Z(35))
    # Real physical moving spatial normal: rotation of orthonormal
    # axes 3 and 4. The bivector generator is induced by this actual
    # frame rotation, not a freely chosen nilpotent carrier matrix.
    K=Z(5);K[3,4]=1;K[4,3]=-1
    def biv(i,j,a,b):
        return K[i,a]*int(j==b)+int(i==a)*K[j,b]-K[i,b]*int(j==a)-int(i==b)*K[j,a]
    L=s.Matrix(10,10,lambda i,j:biv(*P[i],*P[j]))
    big=s.kronecker_product(L,s.eye(10))+s.kronecker_product(s.eye(10),L)
    small=G.inv()*X.T*big*X
    eq(big*X,X*small);eq(small.T*G+G*small,Z(35))
    Pdot=small*P0-P0*small
    eq(Pdot*P0+P0*Pdot,Pdot)
    assert Pdot!=Z(35)
    # If ∂u=small*u+f, then ∂(Pu)-small*Pu=P*f;
    # for independent nonzero jets, transport and source both matter.
    u=s.Matrix([Q(i-7,11) for i in range(35)])
    f=s.Matrix([Q(i+1,13) for i in range(35)])
    eq(Pdot*u+P0*(small*u+f)-small*P0*u,P0*f)
    assert P0*f!=Z(35,1)
    # Same reduced Einstein metric, BEFORE C=0: Ric=-4g+D,
    # D=S(C)+Ered. Schouten = -g/2+(D-g tr D/8)/3.
    g=s.diag(*eta); D=s.Matrix(5,5,lambda i,j:Q((min(i,j)+2)*(max(i,j)+3),19))
    Ric=-4*g+D
    Sch=(Ric-g*s.trace(g*Ric)/8)/3
    eq(Sch,-g/2+(D-g*s.trace(g*D)/8)/3)
    # Mixed wall Weyl from curved Codazzi, in adapted frame:
    # R_nabc = W_nabc - h_ab Sch_nc + h_ac Sch_nb.
    # For the jump, pure constant tension gives [R_nabc]=0,
    # but dropping mixed Ricci defect before subsidiary proof is invalid.
    h=g[:4,:4]; r=D[4,:4]
    defect=s.Matrix([h[a,b]*r[c]/3-h[a,c]*r[b]/3 for a in range(4) for b in range(4) for c in range(b+1,4)])
    assert defect!=Z(24,1)
    print('PASS BR88 actual BR29 rank-nine projector physical frame transport, Schouten source and mixed Codazzi defect')
    print('BR88 boundary: P0*f=0 still requires physical source attachment; no subsidiary uniqueness by projection alone')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['BR85','BR86','BR87','BR88'],required=True)
    p.add_argument('--allocation',choices=['D','E'],default='E')
    p.add_argument('--sector',choices=['metric','gauge'],default='metric')
    a=p.parse_args()
    if a.part=='BR87':br87(a.allocation,a.sector)
    else:{'BR85':br85,'BR86':br86,'BR88':br88}[a.part]()
