#!/usr/bin/env python3
"""Differentiate actual AY/BO acceleration seam; pay gauge corner by lapse and shift jets."""
import sympy as s


def sym(tag):
    return s.Matrix(3,3,lambda i,k:s.Symbol(tag+str(min(i,k))+str(max(i,k))))


def run():
    j,N=s.symbols('j N',real=True,nonzero=True); I=s.eye(3)
    M,D=sym('m'),sym('d'); m=s.trace(M); q=s.trace(M*M); b=s.trace(D)
    Kp=M+j*I/2; Km=M-j*I/2
    Fjump=j*(4+q+m*m)*I-12*j*M*M
    def rn(K):
        tau=s.trace(K); taun=s.trace(D)-2*s.trace(K*K)
        return 2*(D*K+K*D-2*K*K*K)-taun*K-tau*D
    Rjump=(rn(Kp)-rn(Km)-Fjump).applyfunc(s.expand)
    a=s.symbols('a'); ell=-m
    # [E_ab,n]-j E_ab, divided by N. E=Hess N-N(Ric+4gamma).
    res=j*D+2*j*m*M+j*a*I-j*ell*M-j**3*I/4-ell*(j*M-j*m*I)-Rjump-8*j*I
    a0=4+q+3*j*j/4-b
    assert (res-j*(a-a0)*I).applyfunc(s.expand)==s.zeros(3)
    # a0 also sets E_nn to zero on both faces: common value and derivative jump.
    for sign,K in [(1,Kp),(-1,Km)]:
        assert s.expand(a0+sign*j*m-(-b+s.trace(K*K)+4))==0
    # Mixed derivative: keep div M and d m distinct, as well as dN.
    dN=s.Matrix(s.symbols('N0:3')); dm=s.Matrix(s.symbols('dm0:3')); divM=s.Matrix(s.symbols('div0:3'))
    Ric=divM-dm; E=-N*dm-m*dN-M*dN-N*Ric
    Hessjump=3*j*(N*dm+m*dN)+3*j*M*dN
    Ricprimejump=-4*j*Ric
    Ejump=Hessjump-j*N*Ric-N*Ricprimejump
    assert (Ejump+3*j*E).applyfunc(s.expand)==s.zeros(3,1)
    A=2*N*E
    Ajump=2*j*N*E+2*N*Ejump
    assert (Ajump+2*j*A).applyfunc(s.expand)==s.zeros(3,1)
    # Chart x_old=x_new+t² v/2, v=dv=0 at seam: A_new=A+L_v gamma.
    # Choose [v_a,nn]=3j A_na, no normal v jet; after n(y) change [n_yy]=j.
    repaired=Ajump+3*j*A+j*A
    assert (repaired-2*j*A).applyfunc(s.expand)==s.zeros(3,1)
    # normal third lapse jump independently free, kills [A_nn,n].
    R1=s.symbols('R1'); N3=N*(j*a0-2*j*m*m+R1)
    np=N*(-m+j/2); nm=N*(-m-j/2)
    assert s.expand(N3-(np*(a0+j*m)-nm*(a0-j*m))-N*R1)==0
    y,L=s.symbols('y L',positive=True); c=s.symbols('c0:8'); pol=sum(c[i]*y**i for i in range(8))
    J=s.Matrix([pol.diff(y,k).subs(y,end) for end in [0,L] for k in range(4)]).jacobian(c)
    assert s.factor(J.det())==144*L**16
    print('PASS arbitrary noncommuting M,D: tangential, mixed, normal differentiated seam and lapse Hermite rank')
    print('PASS mixed coordinate acceleration weld, initial metric unchanged')

if __name__=='__main__':run()
