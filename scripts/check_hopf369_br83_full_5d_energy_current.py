#!/usr/bin/env python3
"""BR83: FULL five-dimensional actual-ADM first-jet energy-current audit.

Original source owners: BR48 ADM, BR73 positive normal-frame density,
BR76/77 moving material flux, BR80 nonfrozen differential current.

For arbitrary admissible source first jets (N,N_mu,v,v_mu,H,H_mu),
with H positive 4x4 symmetric (including shear), symmetric metric
derivatives and genuine symmetric scalar Hessian U_mu nu:
  X=(1,-v)/N;  D=N sqrt(det H)
  T_mu nu=p_mu p_nu-g_mu nu g^-1(p,p)/2
  J^mu=D T^mu_nu X^nu
  ∂mu J^mu = D{(Box_g u)X(u)+(1/2)T^{mu nu}(L_X g)_mu nu}.
The differential identity is classical and follows from covariant
metric compatibility plus the symmetric scalar Hessian. Here it is
independently calculated on all FIVE axes with exact rational source
jets and all 25 metric/gauge contractions, without freezing the
normal direction, lapse, shift or spatial shear.

All four spatial directions are retained. The 15/5 original metric
and harmonic fields share this SCALAR principal energy identity,
not their different nontrivial Einstein/gauge connection sources.

A finite rational source audit is not a universal Agda theorem, not
a full matrix Einstein symmetrizer, and not a positive boundary
Lopatinski estimate. The actual BR71/72 physical Israel allocation,
BR29 35-component Weyl source and weighted BR31 exterior remain P0.

--part full|channels|moving|negative
"""
import argparse
import sympy as s

R=s.Rational

def geometry(seed):
    N=R(2+seed,3)
    v=s.Matrix([R((i+2)*(seed+1)%13-6,17) for i in range(4)])
    H=s.Matrix([[3,1,0,0],[1,4,1,0],[0,1,5,1],[0,0,1,2]])
    assert all(H[:i,:i].det()>0 for i in range(1,5))
    Hi=H.inv(); Hv=H*v
    g=s.Matrix([[-N*N+(v.T*Hv)[0],*list(Hv)]]).col_join(Hv.row_join(H))
    Gi=s.Matrix([[-1/N**2,*list((v/N**2).T)]]).col_join(
         (v/N**2).row_join(Hi-v*v.T/N**2))
    assert g*Gi==s.eye(5)
    X=s.Matrix([1,*list(-v)])/N
    Nmu=[R((seed+3)*(k+2)%11+1,23+k) for k in range(5)]
    vmu=[s.Matrix([R((i+3)*(k+2)*(seed+1)%17-8,23+i+k)
                for i in range(4)]) for k in range(5)]
    Hmu=[s.Matrix(4,4,lambda i,j:
              R(((min(i,j)+2)*(max(i,j)+3)*(k+seed+2))%23-11,
                29+k+i+j)) for k in range(5)]
    Gmu=[];Xmu=[];logDmu=[]
    for k in range(5):
        z=Hmu[k]*v+H*vmu[k]
        g00=-2*N*Nmu[k]+2*(vmu[k].T*H*v)[0]+(v.T*Hmu[k]*v)[0]
        Gmu.append(s.Matrix([[g00,*list(z.T)]]).col_join(z.row_join(Hmu[k])))
        Xmu.append(-X*Nmu[k]/N+s.Matrix([0,*list(-vmu[k])])/N)
        logDmu.append(Nmu[k]/N+s.trace(Hi*Hmu[k])/2)
        assert Gmu[k]==Gmu[k].T
    assert (X.T*g*X)[0]==-1
    return N,v,H,Hi,g,Gi,X,Gmu,Xmu,logDmu

def check(seed,channel):
    N,v,H,Hi,g,Gi,X,Gmu,Xmu,logDmu=geometry(seed)
    p=s.Matrix([R((seed+2)*(i+channel+1)%19-9,17+i+channel)
                for i in range(5)])
    Hess=s.Matrix(5,5,lambda i,j:
      R(((min(i,j)+2)*(max(i,j)+5)*(seed+channel+1))%19-9,31+i+j))
    assert Hess==Hess.T
    B=Gi*p
    velocity=(X.T*p)[0]
    gradnorm=(p.T*B)[0]
    stress=B*B.T-Gi*gradnorm/2
    J=B*velocity-X*gradnorm/2 # density-UNweighted current
    dX=s.Matrix.hstack(*Xmu)
    Lie=(sum((X[k]*Gmu[k] for k in range(5)),s.zeros(5))
         +dX.T*g+g*dX)
    div=0;box=0
    for k in range(5):
        pk=Hess[:,k]
        Bk=-Gi*Gmu[k]*B+Gi*pk
        velocity_k=(Xmu[k].T*p+X.T*pk)[0]
        norm_k=2*(pk.T*B)[0]-(B.T*Gmu[k]*B)[0]
        Jk=Bk*velocity+B*velocity_k-Xmu[k]*gradnorm/2-X*norm_k/2
        div+=logDmu[k]*J[k]+Jk[k]
        box+=logDmu[k]*B[k]+Bk[k]
    deformation=sum(stress[i,j]*Lie[i,j]
                    for i in range(5) for j in range(5))/2
    assert s.cancel(div-box*velocity-deformation)==0
    physical=(velocity**2+(p[1:5,0].T*Hi*p[1:5,0])[0])/2
    assert physical>=0
    # The un-densitized physical energy equals T(X,X).
    covstress=p*p.T-g*gradnorm/2
    assert (X.T*covstress*X)[0]==physical
    assert J[0]==-physical/N
    return N,v,H,Gi,X,p,J,stress,deformation,physical

def full():
    for seed in range(1,9):check(seed,0)
    print('PASS BR83 eight independent full 5D ADM metric/shift/normal source jets, all 25 stress entries')

def channels():
    for channel in range(20):
        N,v,H,Gi,X,p,J,S,d,E=check((channel%4)+1,channel)
        assert E>=0
    print('PASS BR83 original 15 metric and five gauge scalar-principal normal-frame channels')

def moving():
    N,v,H,Gi,X,p,J,T,d,E=check(3,5)
    F=s.Matrix([-R(1,11),R(1,13),-R(1,17),R(1,19),1])
    z=(F.T*Gi*F)[0]
    assert z>0
    sn=Gi*F/s.sqrt(z)
    physicalStress=Gi.inv()*T*Gi.inv()
    actual=(X.T*physicalStress*sn)[0]
    assert s.simplify((F.T*J)[0]/s.sqrt(z)-actual)==0
    assert s.simplify((X.T*Gi.inv()*sn)[0])!=0
    print('PASS BR83 full 5D actual moving-wall conormal stress and nonzero tilt')

def negative():
    N,v,H,Gi,X,p,J,T,deformation,E=check(4,7)
    assert deformation!=0
    assert E>0
    print('PASS BR83 REFUSAL: physical variable ADM deformation work is not zero')

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--part',choices=('full','channels','moving','negative'),default='full')
    part=parser.parse_args().part
    {'full':full,'channels':channels,'moving':moving,'negative':negative}[part]()
