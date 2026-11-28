import sympy as s
from itertools import product

def exact():
    T,z=s.symbols('T z',positive=True); q=s.symbols('q')
    eta=s.diag(-1,1,1,1,1); g=eta/z**2; gi=z**2*eta
    # Order T,z,x,y,w; scalar projection along x, retain vector currents.
    F=s.Matrix(5,5,lambda a,b:s.Function('F%d%d'%(min(a,b),max(a,b)))(T,z))
    d=lambda h,i: h.diff(T) if i==0 else h.diff(z) if i==1 else q*h if i==2 else 0
    Gamma=lambda a,b,c: (-(a==b)*(c==1)-(a==c)*(b==1)+eta[b,c]*eta[a,1])/z
    def div(A,n,power):
        e=eta[:n,:n]; inv=z**power*e; M=inv*A-s.trace(inv*A)*s.eye(n)/2
        G=lambda a,b,c:power*Gamma(a,b,c)/2
        return s.Matrix([s.expand(sum(d(M[a,j],a)+sum(G(a,a,l)*M[l,j]-G(l,a,j)*M[a,l] for l in range(n)) for a in range(n))) for j in range(n)])
    R=div(F,5,2)
    P=z*z*(F[3,3]+F[4,4])/2
    S=F[:3,:3]+2*P*eta[:3,:3]/z**2
    E=div(S,3,6)
    # transverse scalar EL forcing in Einstein frame: z^4 P (from Ric5 transverse).
    # sign: Box_E psi -4 exp(-4psi) = -z^4 P.
    delta=E-z**4*R[:3,0]
    print('scalar difference',delta.applyfunc(s.simplify))
    assert delta.applyfunc(s.simplify)==s.Matrix([0,-6*z**3*P,0]).applyfunc(s.simplify)
    for I in (3,4):
        J=-2*z**-3*eta[:3,:3]*F[:3,I]
        assert s.simplify(sum(d(J[a],a) for a in range(3))+2*z**-5*R[I])==0
    print('3 scalar + 2 vector source compatibility components PASS')
if __name__=='__main__': exact()
