"""W1 same-action radial reciprocal shell/controller Ward and traction.
Uses ORIGINAL positive reciprocal G(X), determinant one, both signed fluxes.
Radial static EFT, not an Einstein metric or a measured physical controller.
"""
import sympy as s

def eq(x):
    assert s.simplify(s.factor(x))==0, s.factor(x)

def main():
    r=s.symbols('r',positive=True)
    X=s.Function('X')(r)
    q1,q2=s.symbols('q1 q2',real=True)
    q=s.Matrix([q1,q2])
    G=s.Matrix([[1,-X],[-X,1+X*X]])
    GX=G.diff(X)
    assert G.det()==1
    inv=s.Matrix([[1+X*X,X],[X,1]])
    assert G*inv==s.eye(2)
    grad=inv*q/r**2
    flux=r*r*G*grad
    assert flux.applyfunc(s.simplify)==q
    # Radial pressure/traction from the full original field gradient
    traction=s.factor((grad.T*G*grad)[0]/2)
    controller=(grad.T*GX*grad)[0]/2
    # Exact Noether: flux conservation leaves geometric dilution and
    # controller exchange, which cannot be discarded as free gain.
    eq(traction.diff(r)+4*traction/r+controller*X.diff(r))
    assert s.simplify(controller)!=0
    # Work is odd under signed flux cross term; shell transmission alone
    # cannot certify net source/reaction energy or neutral gravitational pickup.
    eq(traction-(q1*q1+(q2+X*q1)**2)/(2*r**4))
    eq(controller-(q1*q2+X*q1*q1)/r**4)
    assert s.factor(controller.subs({q1:1,q2:0,X:s.Rational(3,2)}))!=0
    # Fixed-source external flux is independent of internal X.  Genuine
    # controller dynamics must supply the equal and opposite Ward force.
    force=-controller*X.diff(r)
    eq(force-(traction.diff(r)+4*traction/r))
    print('PASS same-action reciprocal radial flux and controller Ward identity')
    print('PASS signed traction and nonzero omitted-reaction negative control')
    print('OPEN true shell-support stress, controller evolution, Einstein response, receiver')

if __name__=='__main__':main()
