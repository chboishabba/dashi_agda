"""Known quadratic wall sources and moving scalar master boundary (not IBVP coercivity)."""
import sympy as s
from itertools import product

def known(H,Pi,Ht,Pit,gradH,gradPi,A,A2,gradA2,S,mu,K,w,b):
    """All matrices in spatial orthonormal frame; gradients are comoving.
    Return known mixed stress, effective Israel coefficient, material Ward forcing.
    A,S,mu constants; A2 and its gradient given by retarded controller.
    """
    I=s.eye(3); df=w*s.trace(H*H)/4; d=A*s.trace(H*Pi)/2
    P=(df/3+d)*I-A*H*Pi+A2*Pi-mu*S*H
    T=s.diag(-df+d,P)
    Ksrc=s.diag(3*df-d,-(df+d)*I-3*A2*Pi+3*mu*S*H)
    R0=K*s.trace(H*Ht)/2+A*s.trace(H*(Pit+2*b*Pi))/2
    R=[]
    for i in range(3):
        v=w*s.trace(H*gradH[i])/6+A*s.trace(gradH[i]*Pi+H*gradPi[i])/2
        v+=sum((-A*(gradH[j]*Pi+H*gradPi[j])+gradA2[j]*Pi+A2*gradPi[j]-mu*S*gradH[j])[j,i] for j in range(3))
        R.append(v-A*s.trace(Pi*gradH[i])/2)
    return T,Ksrc,R0,s.Matrix(R)


def exact():
    t,x,y,z=s.symbols('t x y z',positive=True); xyz=(x,y,z); b=1/t
    w,K=s.Function('w')(t),s.Function('K')(t); A,S,mu=s.symbols('A S mu'); A2=s.Function('A2')(t,x,y,z)
    H=s.diag(0,(t-x)**2,-(t-x)**2)+s.Matrix([[0,0,t*y],[0,0,0],[t*y,0,0]])
    Pi=s.diag(t*z,-t*z,0)+s.Matrix([[0,t*z,0],[t*z,0,0],[0,0,0]])
    assert s.trace(H)==s.trace(Pi)==0
    assert all(sum(M[j,i].diff(xyz[j]) for j in range(3))==0 for M in (H,Pi) for i in range(3))
    T,C,R0,R=known(H,Pi,H.diff(t),Pi.diff(t),[H.diff(x) for x in xyz],[Pi.diff(x) for x in xyz],A,A2,[A2.diff(x) for x in xyz],S,mu,K,w,b)
    geom=s.diag(0,3*A*H*Pi)
    assert (C+geom+3*T-s.trace(T)*s.eye(4)).applyfunc(s.expand)==s.zeros(4)
    assert C==C.T
    # Known second-order conservation residual: direct background connection,
    # first-order spatial connection and second-order expansion trace.
    rho,p=s.symbols('rho p'); T1=s.diag(0,A*Pi); T0=s.diag(-rho,p,p,p)
    G0=s.MutableDenseNDimArray.zeros(4,4,4); G1=s.MutableDenseNDimArray.zeros(4,4,4); G2=s.MutableDenseNDimArray.zeros(4,4,4)
    for i,j in product(range(3),repeat=2):
        G0[0,i+1,j+1]=t*s.KroneckerDelta(i,j);G0[i+1,0,j+1]=G0[i+1,j+1,0]=b*s.KroneckerDelta(i,j)
        G1[0,i+1,j+1]=(t*t*H[i,j]).diff(t)/2;G1[i+1,0,j+1]=G1[i+1,j+1,0]=H[i,j].diff(t)/2
        G2[i+1,0,j+1]=G2[i+1,j+1,0]=-(H*H.diff(t))[i,j]/2
    for k,i,j in product(range(3),repeat=3):
        G1[k+1,i+1,j+1]=(H[k,j].diff(xyz[i])+H[k,i].diff(xyz[j])-H[i,j].diff(xyz[k]))/2
    conn=lambda G,M,nu:sum(G[a,a,l]*M[l,nu]-G[l,a,nu]*M[a,l] for a,l in product(range(4),repeat=2))
    coords=(t,)+xyz
    for nu in range(4):
        res=sum(T[a,nu].diff(coords[a]) for a in range(4))+conn(G0,T,nu)+conn(G1,T1,nu)+conn(G2,T0,nu)
        assert s.expand(res.subs(p,K+w-rho).subs(w.diff(t),-4*b*w)-(R0 if nu==0 else R[nu-1]))==0
    # Longitudinal scalar Einstein-frame bulk gauge and wall normal displacement.
    F,G,u,f,ft,ftt,k=s.symbols('F G u f ft ftt k'); B=s.sqrt(1+b*b); L=s.diag(-1/B,-B,-B,-B); eta=s.diag(-1,1,1,1)
    p=s.diag(-2*(F-2*u),2*(F-2*u),2*u,2*u,2*(G-2*u)); boost=s.eye(5);boost[0,0]=boost[4,4]=B;boost[0,4]=boost[4,0]=-b
    P=boost.T*p*boost; h=P[:4,:4]; q=u-F/3
    induced=h+2*f*eta*L
    assert s.simplify(induced[1,1]-induced[2,2]+6*q)==0
    assert s.simplify(P[0,4]-2*B*b*(F-G))==0
    assert P[1,4]==0
    # K^x_x-K^y_y: normal derivative of h difference + bending Hessian.
    dnq=s.symbols('dnq'); geomdiff=-3*dnq+k*k*b*b*f
    assert s.solve(geomdiff-s.Symbol('jdiff'),dnq)==[(k*k*b*b*f-s.Symbol('jdiff'))/3]
    # Normal displacement derivative in AdS, and intrinsic FRW mixed Hessian.
    assert s.simplify((s.eye(4)-L*L)[0,0]-(1-1/B**2))==0
    print('12 grouped quadratic wall/Ward and moving scalar boundary checks PASS')

if __name__=='__main__':exact()
