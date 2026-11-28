"""Full action-derived reciprocal spherical shell, massless static comparator.
No physical gravitational shielding, background solution or F8 evolution.
"""
import sympy as s


def zero(A):
    assert A.applyfunc(s.factor)==s.zeros(*A.shape), A


def main():
    c=s.symbols('c',real=True)
    f=s.symbols('f',positive=True) # (a/b)^3, physically 0<f<1
    I=s.eye(2)
    G=s.Matrix([[1,-c],[-c,1+c*c]])
    assert G.det()==1
    zero(G+G.inv()-(2+c*c)*I)
    tau=9/(9+2*(1-f)*c*c)
    A=tau*I
    # B and C are growing and decaying shell amplitudes, with C
    # normalized by inner radius cubed; D by outer radius cubed.
    C=(I-G.inv())*A/3
    B=A-C
    D=B+f*C-I
    zero(B+C-A)
    zero(G*(B-2*C)-A)
    zero(B+f*C-I-D)
    zero(G*(B-2*f*C)-I+2*D)
    zero(D-(tau-1)*I+(1-f)*C)
    assert s.factor(D[1,0]-(1-f)*c*tau/3)==0
    assert s.factor((1/tau-1)-2*(1-f)*c*c/9)==0
    # Reference field has zero cavity gradient for a pure first-channel
    # incident field, but NOT zero local flux throughout the shell.
    e=s.Matrix([1,0])
    zero(A*e-s.Matrix([tau,0]))
    assert s.factor((C*e)[1]+c*tau/3)==0
    assert s.factor((G*C*e)[1]+c*tau/3)==0
    # Reference radial flux is zero at inner boundary, nonzero generally.
    u=s.symbols('u',positive=True) # a^3/r^3
    assert s.factor((G*(B-2*u*C)*e)[1]-2*c*tau*(u-1)/3)==0
    # Controller order sign reversal leaves cavity gain unchanged but
    # changes exterior cross-channel dipole sign.
    assert s.factor(tau.subs(c,-c)-tau)==0
    assert s.factor(D[1,0].subs(c,-c)+D[1,0])==0
    # Independent exact rational fixture,  a/b=1/2, c=6.
    q={f:s.Rational(1,8),c:6}
    assert tau.subs(q)==s.Rational(1,8)
    assert D[1,0].subs(q)==s.Rational(7,32)
    print('PASS full matrix interface, reciprocal gain, signed exterior residual, flux obstruction and rational fixture')
    print('OPEN actual dynamical X profile, reference boundary, mass, stress, metric and F8')

if __name__=='__main__':main()
