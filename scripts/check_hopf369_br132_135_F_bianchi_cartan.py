#!/usr/bin/env python3
"""BR132-135: consume BR29 full subsidiary, restore cyclic wall row,
close frozen constraint energy using dH, and attach Cartan defects.
No variable nonlinear PDE or native kernel acceptance."""
import argparse
from itertools import combinations
import sympy as s
from check_hopf369_br_curvature_energy import carrier,P,eta
Q=s.Rational

def eq(a,b):
    assert (a-b).applyfunc(s.expand)==s.zeros(*a.shape)

def bulk():
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier();pr=G.inv()*X.T;Q0=s.eye(100)-X*pr
    M=[];D=[];trip=list(combinations(range(1,5),3))
    for i in range(1,5):
        L=s.zeros(10)
        for k in range(1,5):
            if k==i:continue
            a=P.index((0,k));b=P.index(tuple(sorted((i,k))));L[a,b]=L[b,a]=1 if i<k else -1
        M.append(s.kronecker_product(L,s.eye(10)))
        Z=s.zeros(50,100)
        for k in range(10):Z[k,10*P.index((0,i))+k]=1
        for j,(u,v,w) in enumerate(trip):
            if i not in (u,v,w):continue
            p,sg=((v,w),1) if i==u else ((u,w),-1) if i==v else ((u,v),1)
            for k in range(10):Z[10+10*j+k,10*P.index(p)+k]=sg
        D.append(Z)
    Dj=s.Matrix.hstack(*(d*X for d in D));Rj=s.Matrix.hstack(*(Q0*a*X for a in M));ids=list(Dj.T.rref()[1]);Dr=Dj[ids,:]
    L=Dr.T.gauss_jordan_solve(Rj.T)[0].T;E0=Dj[:,Dj.rref()[1]];E=E0*E0[ids,:].inv();K=[-d[ids,:]*L for d in D]
    assert Dj.rank()==35 and Rj.rank()==35;eq(L*Dr,Rj);eq(E*Dr,Dj)
    return X,Y,J,A,B,R,pr,Q0,M,D,trip,ids,L,E,K

def graph():
    X,Y,J,A,B,R,pr,Q0,M,D,trip,ids,L,E,K=bulk()
    # Extended symmetric bulk residual graph is NOT invariant on arbitrary
    # independent first jets. Its discrepancy factors through d_sp C_B.
    Gc=L.T*L+E.T*E;N=[];diff=[]
    for i in range(4):
        assert Gc*K[i]!=(Gc*K[i]).T
        T=(-Q0*M[i]*L-Q0*D[i].T*E-L*K[i]).col_join(-D[i]*L-E*K[i])
        assert T.rank()==10;diff.append(T)
        n=s.zeros(10,50);tr=tuple(k for k in range(1,5) if k!=i+1);j=trip.index(tr)
        for a in range(10):n[a,10+10*j+a]=(-1)**i
        N.append(n)
        eq(n*D[i],s.zeros(10,100))
    for i in range(4):
        for j in range(i):eq(N[i]*D[j]+N[j]*D[i],s.zeros(10,100))
    F=s.Matrix.hstack(*diff);Njet=s.Matrix.hstack(*(n*E for n in N))
    assert F.rank()==Njet.rank()==Njet.col_join(F).rank()==10
    T=Njet.T.gauss_jordan_solve(F.T)[0].T;eq(T*Njet,F)
    print('PASS BR132 full BR29 subsidiary graph discrepancy rank 10 factors exactly through spatial dC_B; naive restricted Gram fails')

def wall():
    X,Y,J,A,B,R,pr,Q0,M,D,trip,ids,L,E,K=bulk();An=A[3];AP=5*An-4*An**3;P0=s.eye(35)-An*AP;DnV=D[3][ids,:]*X
    LL=[]
    for a in range(4):
        T=s.zeros(10)
        for i,(b,c) in enumerate(P):
            for k,(d,e) in enumerate(P):
                def unit(v,w):return 1 if (v,w)==(d,e) else -1 if (v,w)==(e,d) else 0
                T[i,k]=((eta[a]*unit(4,c) if b==a else -unit(a,c) if b==4 else 0)+(eta[a]*unit(b,4) if c==a else -unit(b,a) if c==4 else 0))
        LL.append(s.kronecker_product(T,s.eye(10))+s.kronecker_product(s.eye(10),T))
    Kext=pr*(sum((M[i-1]*LL[i] for i in range(1,4)),s.zeros(100))-LL[0])*X
    vals=[DnV*AP*(J*B[i]-A[i]*J)+D[i][ids,:]*X*J for i in range(3)]
    vals.append(DnV*AP*(-J*R-Kext)+sum((D[i-1][ids,:]*LL[i]*X for i in range(1,4)),s.zeros(35)))
    Zall=s.Matrix.hstack(*vals)
    triples=[(a,i,j) for a in range(4) for i,j in combinations(range(1,4),2)]
    Mag=s.zeros(12,100)
    for row,(a,i,j) in enumerate(triples):Mag[row,10*P.index((i,j))+P.index((a,4))]=-1
    Dh=[]
    for k in range(1,4):
        T=s.zeros(12,16)
        for row,(a,i,j) in enumerate(triples):
            if j==k:T[row,4*a+i]=1
            if i==k:T[row,4*a+j]=-1
        Dh.append(T)
    Hw=s.Matrix.hstack(*[-d*Y for d in Dh],Mag*X);Hids=list(Hw.T.rref()[1]);Hred=Hw[Hids,:];Hfull=Hw[:,Hw.rref()[1]];HE=Hfull*Hfull[Hids,:].inv()
    Sc=-L.T*M[3]*L-L.T*D[3].T*E-E.T*D[3]*L
    eq(Sc*DnV*P0,s.zeros(35));Coupling=Hred.T.gauss_jordan_solve((Sc*Zall).T)[0].T;eq(Coupling*Hred,Sc*Zall)
    Qfull=-Mag*L;Qred=Qfull[Hids,:]
    assert Qred.rank()==11 and Qred.T.row_join(Coupling).rank()==12
    assert Qfull.rank()==Qfull.T.row_join(Coupling).rank()==12
    Wmap=Qfull.T.gauss_jordan_solve(Coupling)[0];eq(Qfull.T*Wmap,Coupling)
    S=HE.T*Wmap;eq(S,S.T);assert S.eigenvals()=={-Q(3,2):3,-3:4,-6:3,-9:1}
    assert HE.T.nullspace()[0].T*Wmap==s.zeros(1,11)
    # Actual wall antisymmetric projection residual, not a new unknown.
    hr=s.Matrix(s.symbols('H:12'))
    def hh(a,i,j):return 0 if i==j else hr[triples.index((a,i,j))] if i<j else -hr[triples.index((a,j,i))]
    rr=s.zeros(4)
    for i in range(1,4):rr[i,0]=sum(hh(k,k,i) for k in range(1,4))/2;rr[0,i]=-rr[i,0]
    for i,j in combinations(range(1,4),2):rr[i,j]=-hh(0,i,j)/2;rr[j,i]=-rr[i,j]
    RW=s.Matrix(list(rr)).jacobian(hr)*HE
    # Hodge encode H_{0ij}=eps_ijk e_k, H_{aij}=eps_ijk X_ak,
    # a=1..3, tr X=0. Keep all 11 independent coordinates.
    u=s.Matrix(s.symbols('u:11'));e=u[:3,0];xx=s.zeros(3);keys=[(a,k) for a in range(3) for k in range(3) if (a,k)!=(2,2)]
    for i,(a,k) in enumerate(keys):xx[a,k]=u[3+i]
    xx[2,2]=-xx[0,0]-xx[1,1]
    HF=s.Matrix([sum(s.LeviCivita(i-1,k-1,l)*(e[l] if a==0 else xx[a-1,l]) for l in range(3)) for a,i,k in triples]);T=HF[Hids,:].jacobian(u);eq(HE*T,HF.jacobian(u))
    Gnew=-T.T*S*T;xs=(xx+xx.T)/2;xa=(xx-xx.T)/2
    eq(u.T*Gnew*u,s.Matrix([[Q(3,2)*e.dot(e)+3*s.trace(xs.T*xs)+6*s.trace(xa.T*xa)]]))
    Hodge=s.zeros(3,12)
    for k in range(3):
        for idx,(a,i,j) in enumerate(triples):
            if a==0:Hodge[k,idx]=s.LeviCivita(i-1,j-1,k)
    Esrc=Hodge*Qfull;Rowdiv=s.Matrix.vstack(*[-E[10+10*trip.index((1,2,3))+P.index((a,4)),:] for a in range(1,4)])
    for i in range(3):
        Fphys=-T.T*Wmap.T*Dh[i]*RW*T;sk=Fphys-Fphys.T
        assert sk.rank()==6
        eq(sk[:3,3:],-Q(3,2)*xx[i,:].T.jacobian(u)[:,3:])
        eq(sk[:3,:3],s.zeros(3));eq(sk[3:,3:],s.zeros(8))
        eq(Hodge*Dh[i]*RW*T,s.zeros(3,3).row_join((xx[i,:].T-xx[:,i]).jacobian(u)[:,3:]/2))
    # d_sp H has no curl-M term in the flat principal case. Rowdiv
    # equals the actual spatial Bianchi trace, exactly twice e source.
    eq(Rowdiv,2*Esrc)
    # Integrated tangential work -3/2 e·divT X = -3 e·e_t
    # after using e_t=(divT X-div X)/2+Esrc c and div X=Rowdiv c.
    # Thus the full normal cancellation survives the mass correction.
    Gfinal=Gnew+s.diag(3,3,3,*([0]*8));assert Gfinal.is_positive_definite
    j=Q(-6,5);assert (-j*Gfinal).is_positive_definite
    eq(u.T*Gfinal*u,s.Matrix([[Q(9,2)*e.dot(e)+3*s.trace(xs.T*xs)+6*s.trace(xa.T*xa)]]))
    print('PASS BR133 full 12-row multiplier resolves rank-12 work obstruction; tangential skew rank 6 paid by dH, positive corrected wall mass')

# Small exact exterior algebra oracle, independent polynomial matrices.
def perm_sign(a):return (-1)**sum(a[i]>a[j] for i in range(len(a)) for j in range(i+1,len(a)))

def add(A,B):
    out=dict(A)
    for k,v in B.items():out[k]=out.get(k,s.zeros(*v.shape))+v
    return out
def neg(A):return {k:-v for k,v in A.items()}
def wedge(A,B):
    out={}
    for a,v in A.items():
        for b,w in B.items():
            if set(a)&set(b):continue
            k=tuple(sorted(a+b));z=perm_sign(a+b)*v*w
            out[k]=out.get(k,s.zeros(*z.shape))+z
    return out
def d(A,x):
    out={}
    for a,v in A.items():
        for i,t in enumerate(x):
            if i in a:continue
            k=tuple(sorted((i,)+a));z=perm_sign((i,)+a)*v.diff(t)
            out[k]=out.get(k,s.zeros(*z.shape))+z
    return out
def cov(A,O,x,k):return add(d(A,x),add(wedge(O,A),{p:(-1)**(k+1)*v for p,v in wedge(A,O).items()}))
def feq(A,B):
    for k in set(A)|set(B):
        v=A.get(k);w=B.get(k);v=s.zeros(*w.shape) if v is None else v;w=s.zeros(*v.shape) if w is None else w;eq(v,w)

def exterior():
    x=s.symbols('x:5');I=range(5);m=lambda k:s.Matrix(2,2,lambda i,j:Q(((k+2)*(i+3)*(j+4))%17-8,19+k))
    O={(i,):m(i)*(1+x[i]+x[(i+1)%5]) for i in I}
    R={p:m(i+5)*(1+x[p[0]]*x[p[1]]) for i,p in enumerate(combinations(I,2))}
    F=add(d(O,x),wedge(O,O));E=add(F,neg(R));C=cov(R,O,x,2)
    # End-valued exterior d^2 identities. No torsion-free assumption.
    feq(cov(C,O,x,3),add(wedge(E,R),neg(wedge(R,E))))
    star={}
    for p,v in R.items():
        c=tuple(i for i in I if i not in p);star[c]=perm_sign(p+c)*s.prod(eta[i] for i in p)*v
    feq(wedge(R,star),wedge(star,R))
    D=cov(star,O,x,3)
    feq(cov(D,O,x,4),add(wedge(E,star),neg(wedge(star,E))))
    assert any(v.applyfunc(s.expand)!=s.zeros(2) for v in cov(C,O,x,3).values())
    print('PASS BR134 exact five-dimensional exterior Bianchi subsidiary sources [E,R] and [E,*R] on independent noncommuting forms')

def cartan():
    # On a common induced wall, block Lorentz connection Omega has
    # omega tangent, k tangent-normal, -k^T eta normal-tangent.
    x=s.symbols('x:4');h=s.diag(-1,1,1,1)
    def a(seed,n,m):return s.Matrix(n,m,lambda i,j:Q(((seed+3)*(i+2)*(j+5))%19-9,23+seed))
    om={};kk={};O={};B={};er={};Ef={}
    for i in range(4):
        A=a(i,4,4)*(1+x[i]);om[(i,)]=A-h*A.T*h;k=a(i+5,4,1)*(1+x[(i+1)%4]);kk[(i,)]=-k.T*h
        O[(i,)]=om[(i,)].row_join(k).col_join(kk[(i,)].row_join(s.zeros(1)))
    for i,p in enumerate(combinations(range(4),2)):
        A=a(i+10,4,4)*(1+x[p[0]]);B[p]=A-h*A.T*h;k=a(i+17,4,1)*(1+x[p[1]]);er[p]=-k.T*h
        Ef[p]=B[p].row_join(k).col_join(er[p].row_join(s.zeros(1)))
    # normal-tangent block of D_Omega E = D_omega e + Omega_nt wedge B.
    # H=-mean e, D_Omega E=-D_Omega R. Thus dH = mean dR +
    # mean Omega_nt wedge E_tan, with the actual normal sign retained.
    covE=cov(Ef,O,x,2);nt={p:v[4,:4] for p,v in covE.items()};intr=add(d(er,x),neg(wedge(er,om)))
    feq(nt,add(intr,wedge(kk,B)))
    assert any(v!=s.zeros(1,4) for v in wedge(kk,B).values())
    print('PASS BR135 covariant wall Codazzi defect curl factors through Cartan curvature defect and full Bianchi source')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['graph','wall','exterior','cartan'],required=True)
    {'graph':graph,'wall':wall,'exterior':exterior,'cartan':cartan}[p.parse_args().part]()
