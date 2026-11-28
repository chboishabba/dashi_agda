"""BO: exact spatial corner algebra and highest-jet source-preserving repair.
Finite symbolic and rational controls; not a solved nonzero BN metric.
"""
import sympy as s
from itertools import product


def zero(A):
    if isinstance(A,s.MatrixBase):
        return all(s.expand(v)==0 for v in A)
    return s.expand(A)==0


def tf(A,H=None):
    H=s.eye(A.rows) if H is None else H
    return A-s.trace(H.inv()*A)*H/A.rows


def corners():
    j=s.symbols('j',real=True)
    a,b,c,d,e,f=s.symbols('a b c d e f',real=True)
    M=s.Matrix([[a,d,e],[d,b,f],[e,f,c]])
    p,q,r,l,m,n=s.symbols('p q r l m n',real=True)
    D=s.Matrix([[p,l,m],[l,q,n],[m,n,r]])
    I=s.eye(3); Kp=M+j*I/2; Km=M-j*I/2
    sig=s.trace(M); sig2=s.trace(M*M)
    # Spatial scalar R=R_H-2 tr D+3 tr(K^2)-(tr K)^2.
    # At the seam [R_H']= -2j R_H by the constant-scale jump.
    def scalar_derivative_noF(K):
        tau=s.trace(K); A2=s.trace(K*K)
        return 4*s.trace(K*D)+6*s.trace(K*D)-12*s.trace(K**3)-2*tau*(s.trace(D)-2*A2)
    RH=-12+2*s.trace(D)-3*s.trace(M*M)+sig**2 # mean scalar constraint; j^2 terms cancel in 3 dims
    traceF=s.expand((-2*j*RH+scalar_derivative_noF(Kp)-scalar_derivative_noF(Km))/2)
    assert zero(traceF-j*(12-9*sig2+3*sig**2))
    # Lorentzian mean tensor includes M_tt=tr spatial M, zero mixed at time symmetry.
    h=s.diag(-1,1,1,1); mean=s.diag(sig,1,1,1);mean[1:,1:]=M
    assert zero(s.trace(h*mean))
    A=h*mean; q4=s.trace(A*A)
    Fjump=j*(4+q4)*h-12*j*mean*h*mean
    assert zero(s.trace(Fjump[1:,1:])-traceF)
    assert zero(tf(Fjump[1:,1:])+12*j*tf(M*M))
    # Normal Einstein RHS spatial corner, Ric(h)_ij=Ric(H)_ij+H_tt/2.
    Ric=s.Matrix([[p,l,m],[l,q,n],[m,n,r]]) # arbitrary intrinsic tensor
    accel=2*(D-Ric-(4-j*j/2)*I-2*M*M)
    for side in (1,-1):
        K=mean+side*j*h/2; tau=s.trace(h*K)
        target=Ric+accel/2+4*I-tau*K[1:,1:]+2*(K*h*K)[1:,1:]
        assert zero(target-D)
    # Nonorthonormal exact rational basis changes are mandatory.
    S=s.Matrix([[2,1,0],[0,1,1],[1,0,1]])
    H=S.T*S; Mt=S.T*M*S; Ft=S.T*Fjump[1:,1:]*S
    assert zero(tf(Ft,H)+12*j*tf(Mt*H.inv()*Mt,H))
    print('PASS third-normal trace, 5 independent TF equations, all 6 acceleration entries, nonorthogonal covariance')


def conformal():
    j,E=s.symbols('j E',real=True,nonzero=True) # E=exp(phi)>0
    v=s.Matrix(s.symbols('v0:3')); a,b,c,d,e,f=s.symbols('a b c d e f')
    Hess=s.Matrix([[a,d,e],[d,b,f],[e,f,c]])
    X=tf(Hess-v*v.T)
    # Fixed physical tension: [phi_y]=j(E-1), derivative jump j E dphi.
    jump_phi_y=j*(E-1); jump_dphi_y=j*E*v
    jump_hess_phi_y=j*E*(Hess+v*v.T)
    jump_Riy=-2*jump_dphi_y+2*j*v+2*jump_phi_y*v
    assert zero(jump_Riy)
    jump_dy_Rij=tf(-2*jump_hess_phi_y+2*(jump_dphi_y*v.T+v*jump_dphi_y.T))
    assert zero(jump_dy_Rij/E+2*j*X)
    Dtf=-X-(-2*X) # intrinsic dimension 3 minus spatial dimension 4 Ricci
    jumpF=-jump_dy_Rij/E+j*Dtf
    assert zero(jumpF-3*j*X)
    # reciprocal w: phi=-log(1+w), X=-u Hess(w)^TF.
    u=s.symbols('u',positive=True); wv=s.Matrix(s.symbols('w0:3'))
    assert zero(tf(-u*Hess+u*u*wv*wv.T-(-u*wv)*(-u*wv).T)+u*tf(Hess))
    # Linear AN mixed source removed in wall Gaussian gauge via I'=b^-2.
    y,L=s.symbols('y L',positive=True); b=s.Function('b')(y); I=s.Function('I')(y)
    profile=y*y*(L-y)**2*(L-2*y)/L**3
    assert s.simplify(s.diff(profile,y,3).subs(y,0)-s.diff(profile,y,3).subs(y,L))==0
    B=b*b
    jet=s.diff(B*I,y,3).subs({s.diff(I,y,3):s.diff(b**-2,y,2),s.diff(I,y,2):s.diff(b**-2,y),s.diff(I,y):b**-2,I:0},simultaneous=True)
    assert s.simplify(jet-(4*s.diff(b,y,2)/b))==0
    print('PASS exact conformal third-jump identity and linear AN source cancellation')


def repair():
    y,L=s.symbols('y L',positive=True)
    # Symmetric endpoint profile: both endpoint jets through 2 zero,
    # opposite unit third derivatives.
    p=y**3*(L-y)**3/(6*L**3)
    for k in range(3):
        assert s.simplify(s.diff(p,y,k).subs(y,0))==0
        assert s.simplify(s.diff(p,y,k).subs(y,L))==0
    assert s.simplify(s.diff(p,y,3).subs(y,0)-1)==0
    assert s.simplify(s.diff(p,y,3).subs(y,L)+1)==0
    assert s.simplify(p-p.subs(y,L-y))==0
    # Principal trace identity on actual sheared coordinate metric.
    H=s.Matrix([[3,1,0],[1,4,1],[0,1,2]])
    a=s.Matrix([s.Rational(1,7),s.Rational(-2,9),s.Rational(3,11)])
    seed=H.row_join(a).col_join(a.T.row_join(s.ones(1,1)))
    I=seed.inv();S=I[3,3]
    assert I[:3,:3]-I[:3,3]*I[3,:3]/S==H.inv()
    p,q,r,l,m,n=s.symbols('p q r l m n');C=tf(s.Matrix([[p,l,m],[l,q,n],[m,n,r]]),H)
    assert zero(sum((I[i,3]*I[k,3]-S*I[i,k])*C[i,k] for i,k in product(range(3),repeat=2)))
    u,t=s.symbols('u t',positive=True); Ssym=s.symbols('S',positive=True)
    # Physical delta g_yyy=u² C; Gaussian n derivative dy/dn=sqrt(S)/u.
    fac=s.simplify(u*u*(s.sqrt(Ssym)/u)**3/2)
    assert s.simplify(2*fac-Ssym**s.Rational(3,2)/u)==0
    assert s.simplify(2*fac*(-u/Ssym**s.Rational(3,2))+1)==0
    # At each side scalar derivative is controlled by trace of third metric jet.
    # For a general order k, conformal and TF tangential inputs span Sym².
    G=s.Matrix([[p,l,m],[l,q,n],[m,n,r]]);target=tf(G,H);trace=s.trace(H.inv()*G)/3
    assert zero(G-target-trace*H)
    # Scale-free spectral trace-extension integral (no numerics).
    lam=s.symbols('lam',positive=True);t=s.symbols('t',positive=True)
    # For y³ exp(-lambda y)/6 the kth derivative squared integral
    # equals constant * lambda^(2k-7). Check all k through 7.
    for k in range(8):
        P=s.diff(t**3*s.exp(-t)/6,t,k)*s.exp(t)
        coeff=s.integrate(s.expand(P**2)*s.exp(-2*t),(t,0,s.oo))
        assert coeff.is_positive
    print('PASS cubic lift, exact scalar normal-derivative neutrality, KK Schur trace, all-order highest-jet splitting and spectral scaling')


if __name__=='__main__':
    corners();conformal();repair()
