"""Abstract oscillator response and observation discriminators; no atmospheric apparatus parameters."""
import sympy as s

def run():
    A,B,C,D,w,t,g,k,F=s.symbols('A B C D w t g k F', real=True)
    x=s.symbols('x', nonzero=True)
    # Laurent carrier with independent slow envelope: exact frequency bookkeeping.
    y=s.symbols('y', nonzero=True)
    carrier=(A+B*(y+1/y)/2)*(x+1/x)/2
    square=s.expand(carrier**2)
    assert square.coeff(x,0).coeff(y,2)==B**2/8
    assert square.coeff(x,0).coeff(y,1)==A*B/2
    assert s.expand(square.subs(B,0)).coeff(x,0).coeff(y,2)==0
    # Two passive quadrature observations with equal total intensity but opposite handedness.
    assert s.simplify(s.Abs(1)**2+s.Abs(s.I)**2-2)==0
    assert s.im(s.I)==-s.im(-s.I)
    # Generic slow mode ledger: source work, dissipation and storage are distinct.
    q,v,j=s.symbols('q v j', real=True)
    U=(v*v+k*q*q)/2
    assert s.expand(s.diff(U,q)*v+s.diff(U,v)*(j-g*v-k*q)-j*v+g*v*v)==0
    # A large susceptibility is not itself a source of work.
    assert s.expand((k-w*w+s.I*g*w)*(k-w*w-s.I*g*w))==s.expand((k-w*w)**2+g*g*w*w)
    assert 7800-1000*s.Rational(783,100)==-30
    assert s.Rational(783,200)*2==s.Rational(783,100)
    print('9/9 exact symbolic assertions PASS; abstract response only')
if __name__=='__main__': run()
