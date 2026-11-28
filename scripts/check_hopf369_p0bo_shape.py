"""BO: full wall shape and highest-time-jet normal recursion.
Exact symbolic controls, not a continuum evolution or analytic radius.
"""
import sympy as s
from itertools import product


def sym(name,n=3):
    vals=iter(s.symbols(name+':'+str(n*(n+1)//2)))
    A=s.zeros(n)
    for i in range(n):
        for k in range(i,n):A[i,k]=A[k,i]=next(vals)
    return A


def zero(A):
    if isinstance(A,s.MatrixBase):return all(s.expand(v)==0 for v in A)
    return s.expand(A)==0


def gauss_codazzi():
    I=s.diag(-1,1,1,1); P=sym('p'); U=sym('u'); Msp=sym('m')
    hdot=s.zeros(4);hdot[1:,1:]=2*P
    hdd=s.zeros(4);hdd[1:,1:]=2*U
    dI=-I*hdot*I
    T=lambda l,i,k: (hdot[l,k] if i==0 else 0)+(hdot[l,i] if k==0 else 0)-(hdot[i,k] if l==0 else 0)
    Td=lambda l,i,k: (hdd[l,k] if i==0 else 0)+(hdd[l,i] if k==0 else 0)-(hdd[i,k] if l==0 else 0)
    G={(a,i,k):sum(I[a,l]*T(l,i,k)/2 for l in range(4)) for a,i,k in product(range(4),repeat=3)}
    Gd={(a,i,k):sum((dI[a,l]*T(l,i,k)+I[a,l]*Td(l,i,k))/2 for l in range(4)) for a,i,k in product(range(4),repeat=3)}
    R=s.Matrix(4,4,lambda i,k:sum((Gd[a,i,k] if a==0 else 0)-(Gd[a,i,a] if k==0 else 0)+sum(G[a,a,l]*G[l,i,k]-G[a,k,l]*G[l,i,a] for l in range(4)) for a in range(4)))
    theta=s.trace(P);td=s.trace(U-2*P*P)
    assert zero(R[1:,1:]-(U+theta*P-2*P*P))
    assert zero(R[0,0]+td+s.trace(P*P))
    assert zero(R[0,1:]) and zero(s.trace(I*R)-(2*td+theta**2+s.trace(P*P)))
    sigma=s.trace(Msp);B=s.Matrix(s.symbols('B:3'));Bt=s.Matrix(s.symbols('Bt:3'));sigmat=s.symbols('sigmat')
    M=s.zeros(4);M[0,0]=sigma;M[0,1:]=B.T;M[1:,0]=B;M[1:,1:]=Msp
    Md=s.zeros(4);Md[0,0]=sigmat;Md[0,1:]=Bt.T;Md[1:,0]=Bt
    div=s.Matrix([sum(I[i,i]*((Md[i,k] if i==0 else 0)-sum(G[l,i,i]*M[l,k]+G[l,i,k]*M[i,l] for l in range(4))) for i in range(4)) for k in range(4)])
    assert zero(div[0]+sigmat+theta*sigma+s.trace(P*Msp))
    assert zero(div[1:,0]+Bt+theta*B)
    a=s.symbols('a');A=P-theta*s.eye(3)/3;Q=Msp-sigma*s.eye(3)/3
    assert zero(s.trace(P*Msp)-theta*sigma/3-s.trace(A*Q))
    assert zero(theta**2+s.trace(P*P)-12*(theta/3)**2-s.trace(A*A))
    assert zero(s.trace((I*M)**2)-(4*sigma**2/3+s.trace(Q*Q)-2*B.dot(B)))
    print('PASS general noncommuting shape Gauss and Codazzi time blocks, full trace decomposition')


def recursion():
    I=s.diag(-1,1,1,1); C=sym('c',4)
    # Twice the principal Ricci variation, pure t covector. This is the
    # highest pure time derivative map in h_nn=2 Ric(h)+lower terms.
    def S(C):
        return s.Matrix(4,4,lambda a,b:sum(I[i,i]*(int(i==0 and a==0)*C[b,i]+int(i==0 and b==0)*C[a,i]-int(i==0)*C[a,b]-int(a==0 and b==0)*C[i,i]) for i in range(4)))
    T=S(C)
    assert zero(T[1:,1:]-C[1:,1:])
    assert zero(T[0,1:]) and zero(T[0,0]+s.trace(C[1:,1:]))
    assert zero(S(T)-T)
    # Reuse the idempotent principal map at every normal recursion order.
    for r in range(1,13):
        assert zero(T[1:,1:]-C[1:,1:]);T=S(T)
    # Mean F changes by H0 Q2 when only M_sp,tt changes at fixed H and lower jets.
    Q2=sym('q');Q2=Q2-s.trace(Q2)*s.eye(3)/3
    k2=s.zeros(4);k2[1:,1:]=Q2
    assert zero(S(k2)[1:,1:]-Q2)
    print('PASS pure-time normal principal map idempotence, 12 recursion levels, mean-third-jet rank five')


if __name__=='__main__':
    gauss_codazzi();recursion()
