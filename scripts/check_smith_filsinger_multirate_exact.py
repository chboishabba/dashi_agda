"""Source-independent spectral and work discriminators; not device calibration."""
import sympy as S

def run():
    x,y,a,b,c,d=S.symbols('x y a b c d', real=True)
    # Independent carrier and slow phase variables; Laurent indices avoid aliasing.
    v=a*(x+1/x)/2+b*(y+1/y)/2
    q=S.expand(c*v+d*v**2)
    assert q.coeff(x,1).coeff(y,1)==d*a*b/2
    assert q.coeff(x,1).coeff(y,-1)==d*a*b/2
    assert S.expand(q.subs(b,0)).coeff(y,1)==0
    # A pure fast tone cannot produce a slow subharmonic via memoryless polynomial.
    for k in range(1,9):
        p=S.expand(((x**1000+x**-1000)/2)**k)
        assert p.coeff(x,1)==0
    # Existing finite-line material law: U_p=p²/(2chi)+beta*p⁴/4.
    p,chi,beta,eta,V,pdot,chidot=S.symbols('p chi beta eta V pdot chidot', real=True)
    U=p*p/(2*chi)+beta*p**4/4
    residual=S.diff(U,p)*pdot+S.diff(U,chi)*chidot-(V*pdot-eta*pdot**2-p*p*chidot/(2*chi**2))
    assert S.simplify(residual.subs(V,eta*pdot+p/chi+beta*p**3))==0
    # Two-tone difference frequency and exact nominal detuning.
    f=S.Rational(783,100); carrier=S.Integer(7800)
    assert carrier-1000*f==-30
    assert carrier- (carrier-f)==f
    # Forward/backward phase increments remain separate from temporal frequency.
    k1,k2,w1,w2,z,t=S.symbols('k1 k2 w1 w2 z t', real=True)
    assert S.expand((k1*z-w1*t)-(k2*z-w2*t)-((k1-k2)*z-(w1-w2)*t))==0
    print('15 exact symbolic checks PASS; no original physical calibration')
if __name__=='__main__':run()
