#!/usr/bin/env python3
"""BR29: full zero-speed Israel propagation and exact subsidiary seam audit.
Full Bianchi propagation at the interface is NOT inferred from projected energy.
"""
import sympy as s
from itertools import combinations
from check_hopf369_br_curvature_energy import carrier,P,eta,q


def run():
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier(); proj=G.inv()*X.T; Q=s.eye(100)-X*proj
    An=A[3]; AP=5*An-4*An**3; P0=s.eye(35)-An*AP
    assert P0*P0==P0 and P0.rank()==9 and P0*An==s.zeros(35)
    def mx(i):
        L=s.zeros(10)
        for k in range(1,5):
            if k==i:continue
            e=P.index((0,k));b=P.index(tuple(sorted((i,k))));L[e,b]=L[b,e]=1 if i<k else -1
        return s.kronecker_product(L,s.eye(10))
    M=[mx(i) for i in range(1,5)]
    def gen(a):
        T=s.zeros(10)
        for i,(b,c) in enumerate(P):
            for k,(d,e) in enumerate(P):
                def unit(v,w):return 1 if (v,w)==(d,e) else -1 if (v,w)==(e,d) else 0
                T[i,k]=((eta[a]*unit(4,c) if b==a else -unit(a,c) if b==4 else 0)+(eta[a]*unit(b,4) if c==a else -unit(b,a) if c==4 else 0))
        return s.kronecker_product(T,s.eye(10))+s.kronecker_product(s.eye(10),T)
    LL=[gen(a) for a in range(4)]
    for L0 in LL:assert Q*L0*X==s.zeros(100,35)
    rawK=sum((M[i-1]*LL[i] for i in range(1,4)),s.zeros(100))-LL[0]
    Kext=proj*rawK*X
    for i in range(3):assert P0*(A[i]*J-J*B[i])==s.zeros(35,9)
    assert P0*(Kext+J*R)==s.zeros(35)
    z=s.Matrix(s.symbols('z:9')); MM=s.Matrix(4,4,list(Y*z))
    LM=[sum((MM[a,b]*eta[b]*LL[b] for b in range(4)),s.zeros(100)) for a in range(4)]
    KM=proj*(sum((M[i-1]*LM[i] for i in range(1,4)),s.zeros(100))-LM[0])*X
    assert (P0*KM*J*z).applyfunc(s.expand)==s.zeros(35,1)
    # Full Maxwell spatial constraints: divergence of E and curl of B.
    D=[]; trip=list(combinations(range(1,5),3))
    for i in range(1,5):
        Z=s.zeros(50,100)
        for k in range(10):Z[k,10*P.index((0,i))+k]=1
        for j,(u,v,w) in enumerate(trip):
            if i not in (u,v,w):continue
            pr,sg=((v,w),1) if i==u else ((u,w),-1) if i==v else ((u,v),1)
            for k in range(10):Z[10+10*j+k,10*P.index(pr)+k]=sg
        D.append(Z)
    for i in range(4):
        assert M[i]**2+D[i].T*D[i]==s.eye(100)
        assert D[i]*M[i]==s.zeros(50,100)
        for j in range(i):
            assert M[i]*M[j]+M[j]*M[i]+D[i].T*D[j]+D[j].T*D[i]==s.zeros(100)
            assert D[i]*M[j]+D[j]*M[i]==s.zeros(50,100)
    # R_b=(I-P)M(d)W, C_b=D(d)W. Extended subsidiary matrices symmetric.
    for i in range(4):
        U=(-Q*M[i]*Q).row_join(-Q*D[i].T).col_join((-D[i]*Q).row_join(s.zeros(50)))
        assert U==U.T
    Dj=s.Matrix.hstack(*(d*X for d in D)); Rj=s.Matrix.hstack(*(Q*a*X for a in M))
    assert Dj.rank()==35 and Rj.rank()==35 and Dj.col_join(Rj).rank()==35
    ids=list(Dj.T.rref()[1]); Dr=Dj[ids,:]; L=Dr.T.gauss_jordan_solve(Rj.T)[0].T
    assert L*Dr==Rj
    E0=Dj[:,Dj.rref()[1]]; E=E0*E0[ids,:].inv()
    K=[-d[ids,:]*L for d in D]; Kn=K[3]; Pc=4*Kn**2
    assert Kn.eigenvals()=={-s.Rational(1,2):8,s.Rational(1,2):8,0:19} and Pc*Pc==Pc
    Dnv=D[3][ids,:]*X
    vals=[Dnv*AP*(J*B[i]-A[i]*J)+D[i][ids,:]*X*J for i in range(3)]
    vals.append(Dnv*AP*(-J*R-Kext)+sum((D[i-1][ids,:]*LL[i]*X for i in range(1,4)),s.zeros(35)))
    Zall=s.Matrix.hstack(*vals); Z=Pc*Zall
    assert Pc*Dnv*P0==s.zeros(35)
    # Independent wall spatial Codazzi residual H_{aij}=W_{naij}-D_j M_ai+D_i M_aj.
    triples=[(a,i,j) for a in range(4) for i,j in combinations(range(1,4),2)]
    Dmag=s.Matrix([W(4,a,i,j) for a,i,j in triples]).jacobian(q)*V
    Dh=[]; Mag=s.zeros(12,100)
    for row,(a,i,j) in enumerate(triples):Mag[row,10*P.index((i,j))+P.index((a,4))]=-1
    assert Mag*X==Dmag and Mag*M[3]==s.zeros(12,100)
    assert Mag*rawK*X*J==s.zeros(12,9)
    for k in range(1,4):
        T=s.zeros(12,16)
        for row,(a,i,j) in enumerate(triples):
            if j==k:T[row,4*a+i]=1
            if i==k:T[row,4*a+j]=-1
        Dh.append(T)
    Hw=s.Matrix.hstack(*[-d*Y for d in Dh],Dmag)
    assert Hw.rank()==11 and Z.rank()==8 and Hw.col_join(Z).rank()==11
    Hcols=Hw[:,Hw.rref()[1]]; Hids=list(Hcols.T.rref()[1]); HE=Hcols*Hcols[Hids,:].inv()
    Hred=Hw[Hids,:]; Zmap=Hred.T.gauss_jordan_solve(Z.T)[0].T
    assert Zmap*Hred==Z
    # Extended subsidiary energy flux, restricted to algebraic jet graph.
    Sc=-L.T*M[3]*L-L.T*D[3].T*E-E.T*D[3]*L
    assert Sc.rank()==22 and Sc*Dnv*P0==s.zeros(35)
    Coupling=Hred.T.gauss_jordan_solve((Sc*Zall).T)[0].T
    assert Coupling*Hred==Sc*Zall and Coupling.rank()==11
    # Wall residual of symmetric projection: antisymmetry from spatial curl.
    hr=s.Matrix(s.symbols('H:12'))
    def hh(a,i,j):return 0 if i==j else hr[triples.index((a,i,j))] if i<j else -hr[triples.index((a,j,i))]
    rr=s.zeros(4)
    for i in range(1,4):rr[i,0]=sum(hh(k,k,i) for k in range(1,4))/2;rr[0,i]=-rr[i,0]
    for i,j in combinations(range(1,4),2):rr[i,j]=-hh(0,i,j)/2;rr[j,i]=-rr[i,j]
    RW=s.Matrix(list(rr)).jacobian(hr)*HE
    BH=[d[Hids,:]*RW for d in Dh]
    assert BH[0].eigenvals()=={-s.Rational(1,2):2,s.Rational(1,2):2,0:7}
    for a in BH:assert (RW.T*RW)*a==((RW.T*RW)*a).T
    # Negative control: no constant wall-only Gram cancels this chosen
    # extended bulk subsidiary flux using the actual wall magnetic source.
    Qwall=-Mag[Hids,:]*L
    assert Qwall.rank()==11 and Qwall.T.row_join(Coupling).rank()==12
    print('PASS zero-speed jump propagation, including general quadratic mean term')
    print('PASS full Maxwell subsidiary identities, rank-35 residual factor, rank-8 active constraint seam factor')
    print('PASS exact constraint-work factor rank 11; selected separated subsidiary energy obstruction rank 12')

if __name__=='__main__':run()
