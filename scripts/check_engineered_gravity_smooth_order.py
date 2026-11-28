"""Smooth order and massive spherical transfer from the completed kinetic block.
Conditional EFT; no microscopic material or full gravitational solution.
"""
import sympy as s


def eq(a,b=0):
    assert s.factor(s.simplify(a-b))==0,(a,b)


def check():
    r=s.symbols('r',positive=True)
    x=s.Function('X')(r)
    q=s.Matrix([s.Function('u')(r),s.Function('v')(r)])
    l,M=s.symbols('lambda M',positive=True)
    c=l*x
    G=s.Matrix([[1,-c],[-c,1+c*c]])
    V=s.Matrix([[s.Symbol('m1',positive=True)**2,0],[0,s.Symbol('m2',positive=True)**2]])
    # l=1 angular harmonics; p=r² G q'. The radial generator is Hamiltonian.
    J=s.zeros(2).row_join(s.eye(2)).col_join((-s.eye(2)).row_join(s.zeros(2)))
    L=s.zeros(2).row_join(G.inv()/r**2).col_join((2*G+r*r*V).row_join(s.zeros(2)))
    assert (L.T*J+J*L).applyfunc(s.simplify)==s.zeros(4)
    p=r*r*G*q.diff(r)
    E=(r*r*(q.diff(r).T*G*q.diff(r))[0]+(q.T*(2*G+r*r*V)*q)[0])/2
    # On the radial field equations, the derivative of the boundary work
    # pays the entire positive radial energy, with no missing angular term.
    residual=p.diff(r)-(2*G+r*r*V)*q
    eq(s.diff((q.T*p)[0],r)-2*E,(q.T*residual)[0])
    # Local field backreaction for q(r) cos(theta), with X radial.
    # mu=cos(theta); grad products contain mu² and 1-mu².
    mu=s.symbols('mu',real=True)
    Gx=G.diff(x)
    A=(q.diff(r).T*Gx*q.diff(r))[0]/2
    B=(q.T*Gx*q)[0]/(2*r*r)
    drive=A*mu*mu+B*(1-mu*mu)
    P2=(3*mu*mu-1)/2
    eq(drive,(A+2*B)/3+2*(A-B)*P2/3)
    # A radial X equation can only satisfy the full local equation when
    # the quadrupole vanishes or a controller supplies its opposite.
    U=s.Function('U')
    J0=-M*(x.diff(r,2)+2*x.diff(r)/r)+s.diff(U(x),x)+(A+2*B)/3
    eq(-M*(x.diff(r,2)+2*x.diff(r)/r)+s.diff(U(x),x)+drive-J0,2*(A-B)*P2/3)
    # Exact nonzero quadrupole from the previously accepted sharp shell.
    t=s.Rational(1,8); a=s.Rational(1,2); chi=s.Integer(6)
    G0=s.Matrix([[1,-chi],[-chi,1+chi*chi]])
    C=(s.eye(2)-G0.inv())*s.Matrix([t,0])/3
    B0=s.Matrix([t,0])-C
    q0=B0*r+C*a**3/r**2
    Gx0=Gx.subs({x:chi,l:1})
    A0=(q0.diff(r).T*Gx0*q0.diff(r))[0]/2
    B1=(q0.T*Gx0*q0)[0]/(2*r*r)
    Q=s.factor(2*(A0-B1)/3)
    assert Q.subs(r,s.Rational(3,4))!=0
    print('sharp shell order quadrupole at r=3/4:',Q.subs(r,s.Rational(3,4)))
    # Mass term destroys the automatic reciprocal scalar reduction unless
    # the full generalized eigenproblem and exterior matching agree.
    assert (G*V-V*G)[0,1]!=0
    print('PASS spherical Hamiltonian, energy, angular backreaction and massive noncommutation')

if __name__=='__main__':check()
