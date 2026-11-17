"""Exact plane-stratified 4x4 Maxwell tangential generator with arbitrary
in-plane kx,ky and full 3x3 complex dielectric tensor. Longitudinal Ez and
Hz are eliminated using curl laws. Finite source sheet/propagating outgoing
response; NOT full physical 3D inverse Fourier dyadic or measured solar work.
"""
import sympy as S
from smith_filsinger_tangential_maxwell_sympy import three_layer_tangential_transfer
from smith_filsinger_radiation_green_sympy import R,F,flux_z,sheet_power_identity
I=S.I

def oblique_generator(w,kx,ky,mu,eps):
    w,kx,ky,mu=map(S.sympify,(w,kx,ky,mu))
    eps=S.Matrix(eps)
    if eps.shape!=(3,3):raise ValueError("3x3 permittivity required")
    if w==0 or mu==0 or eps[2,2]==0:
        raise ValueError("nonzero omega mu epsilon_zz required")
    Ex,Ey,Hx,Hy=S.symbols("Ex Ey Hx Hy")
    Hz=(kx*Ey-ky*Ex)/(w*mu)
    Ez=((-kx*Hy+ky*Hx)/w-eps[2,0]*Ex-eps[2,1]*Ey)/eps[2,2]
    D=eps*S.Matrix([Ex,Ey,Ez])
    deriv=S.Matrix([I*w*mu*Hy+I*kx*Ez,
                    I*ky*Ez-I*w*mu*Hx,
                    I*kx*Hz-I*w*D[1],
                    I*ky*Hz+I*w*D[0]])
    return S.simplify(deriv.jacobian(S.Matrix([Ex,Ey,Hx,Hy])))

def tilted_hall_permittivity(base,hall,b):
    """Hermitian lossless gyrotropic eps=base I + i hall [b]_cross."""
    bx,by,bz=map(S.sympify,b)
    B=S.Matrix([[0,-bz,by],[bz,0,-bx],[-by,bx,0]])
    return S.sympify(base)*S.eye(3)+I*S.sympify(hall)*B

def outgoing_admittance_2d(omega,kx,ky,mu,epsilon):
    w,kx,ky,m,e=map(S.sympify,(omega,kx,ky,mu,epsilon))
    if any(a.is_positive is not True for a in (w,m,e)):
        raise ValueError("positive lossless exterior parameters required")
    q2=S.simplify(w*w*m*e-kx*kx-ky*ky)
    if q2.is_positive is not True:
        raise ValueError("strict outgoing propagating q_z required")
    q=S.sqrt(q2)
    return S.Matrix([[-kx*ky,-(q*q+ky*ky)],
                     [q*q+kx*kx,kx*ky]])/(w*m*q)

def oblique_sheet_green(T,omega,kx,ky,mu_bottom=1,eps_bottom=1,
                       mu_top=1,eps_top=1):
    Yb=outgoing_admittance_2d(omega,kx,ky,mu_bottom,eps_bottom)
    Yt=outgoing_admittance_2d(omega,kx,ky,mu_top,eps_top)
    A,B,C,D=T[:2,:2],T[:2,2:],T[2:,:2],T[2:,2:]
    Q=A-B*Yb;N=C-D*Yb
    boundary=S.simplify(R*(N-Yt*Q))
    if boundary.det()==0:raise ValueError("singular outgoing source boundary")
    Eb=S.simplify(boundary.inv())
    Et=S.simplify(Q*Eb)
    return dict(upper_E=Et,lower_E=Eb,
                upper_H=S.simplify(Yt*Et),lower_H=S.simplify(-Yb*Eb),
                inside_H=S.simplify(N*Eb),boundary_matrix=boundary,
                upper_Y=Yt,lower_Y=Yb)
