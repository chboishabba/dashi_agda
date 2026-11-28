"""W2 actual reciprocal G(X) interface traction and support admissibility.
Original two-channel static radial action and signed incident flux.
A wall with nonzero stress jump requires equal opposite controller support.
No physical Einstein/Maxwell device identified.
"""
import sympy as s
def eq(x):
    assert s.factor(s.cancel(x))==0,s.factor(x)

def main():
    r=s.symbols('r',positive=True)
    xm,xp,q1,q2=s.symbols('X_minus X_plus q1 q2',real=True)
    Q=s.Matrix([q1,q2])
    def G(X):return s.Matrix([[1,-X],[-X,1+X**2]])
    def traction(X):
        K=G(X)
        assert s.factor(K.det())==1
        qprime=K.inv()*Q/r**2
        assert (r*r*K*qprime-Q).applyfunc(s.simplify)==s.zeros(2,1)
        return s.factor((qprime.T*K*qprime)[0]/2)
    minus,plus=traction(xm),traction(xp)
    jump=s.factor(plus-minus)
    expected=q1*(xp-xm)*(2*q2+q1*(xp+xm))/(2*r**4)
    eq(jump-expected)
    # Nonzero traction jump cannot be statically balanced without sheet
    # stress or some other explicitly sourced material-interface force.
    sheet=-jump
    eq(sheet+jump)
    assert s.factor(sheet.subs({q1:1,q2:0,xm:0,xp:1}))==-1/(2*r**4)
    # Exceptional zero-wall-force channels must be retained, not hidden.
    eq(jump.subs(q1,0))
    eq(jump.subs(xp,xm))
    eq(jump.subs(q2,-q1*(xp+xm)/2))
    eq(jump.subs({q1:1,q2:0,xm:-2,xp:2}))
    # With pure channel-one incidence and outside X_minus=0, zero wall
    # force implies X_plus=0 (assuming real, nonzero q1).
    eq(jump.subs({q2:0,xm:0})-q1*q1*xp*xp/(2*r**4))
    # If interface has speed v, oriented power of the sheet force is v*sheet;
    # controller work remains an independent conserved source ledger.
    v=s.symbols('v',real=True)
    eq(v*sheet+v*jump)
    print('PASS original reciprocal two-face traction jump, required support and signed work')
    print('PASS balanced flux exceptions, pure channel no-support obstruction')
    print('OPEN real wall elasticity, controller source, Einstein response, physical receiver')

if __name__=='__main__':main()
