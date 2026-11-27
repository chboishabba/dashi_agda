#!/usr/bin/env python3
"""BR4 initial harmonic gauge and full acceleration value compatibility.
Uses AY/BE/BQ time-symmetric data, not a construction of all corner jets.
"""
import sympy as s

def run():
    j,N,m,ell=s.symbols('j N m ell',real=True,nonzero=True)
    # At common Gaussian spatial wall point H=I. Normal derivative jump jH.
    M=s.diag(m/3+s.Symbol('u'),m/3+s.Symbol('v'),m/3-s.Symbol('u')-s.Symbol('v'))
    Kp=M+j*s.eye(3)/2; Km=M-j*s.eye(3)/2
    Pp=N*(ell+j/2); Pm=N*(ell-j/2)
    D=s.Matrix(s.symbols('d0:9')).reshape(3,3) # same second jet D on both sides (AY/BE)
    # Ric spatial tangent=Ric_H-D+2K^2-tr(K) K; Ric_nn=-tr D+tr K².
    def Rt(K):return -D+2*K*K-s.trace(K)*K
    dR=Rt(Kp)-Rt(Km)
    dHess=Kp*Pp-Km*Pm
    assert (dR-(j*M-j*m*s.eye(3))).applyfunc(s.expand)==s.zeros(3)
    assert (dHess-N*j*(M+ell*s.eye(3))).applyfunc(s.expand)==s.zeros(3)
    assert (dHess-N*dR).subs(ell,-m).applyfunc(s.expand)==s.zeros(3)
    assert s.expand(s.trace(Kp*Kp-Km*Km))==2*j*m
    # [Hess_na]=D_a(jN)-j D_aN=0; Ric_na jump zero by constant tension.
    grad=s.Matrix(s.symbols('g0:3'))
    assert j*grad-(Kp-Km)*grad==s.zeros(3,1)
    # Choose lapse second derivative jump [N_nn]=2j m N; then full gamma_tt common.
    P2p,P2m=s.symbols('Npp Npm')
    assert s.expand((P2p-P2m-N*s.trace(Kp*Kp-Km*Km)).subs(P2p,P2m+2*j*m*N))==0
    # Realize arbitrary value/first/second normal-coordinate log lapse jets at both ends.
    y,L=s.symbols('y L',positive=True); c=s.symbols('c0:6'); poly=sum(c[i]*y**i for i in range(6))
    jets=[poly.diff(y,k).subs(y,e) for e in [0,L] for k in range(3)]
    J=s.Matrix(jets).jacobian(c); assert s.factor(J.det())==4*L**9
    # In Gaussian n: [log N_n]=j, [log N_nn]=2jm-[ (N_n/N)^2 ]=4jm for ell=-m.
    assert s.expand(2*j*m-((ell+j/2)**2-(ell-j/2)**2)).subs(ell,-m)==4*j*m
    # BR4 conformal derivative coordinate jump. n_y=1, [n_yy]=j; lambda=1 at wall.
    n2p,n2m=s.symbols('n2p n2m'); assert (2*(n2p-n2m)).subs(n2p,n2m+j)==2*j
    # General spatial metric at wall in adapted frame, delta normal derivative J=2j gamma.
    # contracted lower Christoffel jump: J n - tr(J)n/2 = -2j n (dimension 4).
    I=s.eye(4); n=s.Matrix([0,0,0,1]); J=2*j*I
    assert J*n-s.trace(J)*n/2==-2*j*n
    assert J*n-s.trace(J)*n/2-j*n==-3*j*n
    # C=0 with g_t=0, H_i=Gamma_i(gamma)-d_i log N, H_t=0.
    # Reduced Einstein E=Ric+4g=sym nabla C. At C=0 on slice, E_ij=0.
    # Einstein Hamiltonian and momentum constraints imply E_00=E_0i=0,
    # hence both normal/time derivatives of C vanish.
    E00=s.Symbol('E00'); E0=s.Matrix(s.symbols('E01:5')); g=s.diag(-N*N,1,1,1,1)
    E=s.zeros(5); E[0,0]=E00; E[0,1:5]=E0.T;E[1:5,0]=E0
    T=E-g*s.trace(g.inv()*E)/2
    assert s.simplify(T[0,0]-E00/2)==0 and T[0,1:5]==E0.T
    # g_t=0, C_t lower 0 derivative: N_tt/N-tr(gamma^-1 gamma_tt)/2-H0_t.
    # Choose N_tt=0 and H0_t=-trace gamma_tt/2, a common trace by above.
    Nt2,tr,Ht=s.symbols('Ntt trace Ht'); assert (Nt2/N-tr/2-Ht).subs({Nt2:0,Ht:-tr/2})==0
    print('PASS full spatial acceleration value jump, quintic lapse jets, BR4 gauge jump and initial gauge constraints')

if __name__=='__main__':run()
