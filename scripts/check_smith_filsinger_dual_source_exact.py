"""Abstract two-source energy and geometry discriminators, not a device model."""
import sympy as s

def run():
    count=0
    q,v,k,g,jd,jn=s.symbols('q v k g jd jn', real=True)
    U=(v*v+k*q*q)/2
    rhs=s.diff(U,q)*v+s.diff(U,v)*(jd+jn-g*v-k*q)
    for drive,nat in [(jd,0),(0,jn),(jd,jn),(0,0)]:
        assert s.expand(rhs.subs({jd:drive,jn:nat})-v*(drive+nat)+g*v*v)==0; count+=1
    # Identical state forcing does not identify the supplying port.
    a=s.symbols('a',real=True)
    assert s.expand((jd+jn).subs({jd:jd+a,jn:jn-a})-jd-jn)==0;count+=1
    # Nominal harmonic arithmetic, not observed electrical lock.
    f=s.Rational(783,200)
    assert 2*f==s.Rational(783,100);count+=1
    assert 2000*f==7830;count+=1
    assert 7800-2000*f==-30;count+=1
    # Integer multiples and difference tones coexist in a sparse phase lattice.
    x,y=s.symbols('x y',nonzero=True)
    p=x+1/x; z=y+1/y
    assert s.expand(p**2).coeff(x,2)==1;count+=1
    assert s.expand((p+z)**2).coeff(x,1).coeff(y,-1)==2;count+=1
    # Geometry alone does not impose a half-frequency relation.
    phi=(1+s.sqrt(5))/2
    assert s.simplify(phi**2-phi-1)==0;count+=1
    assert s.simplify(phi-2)!=0;count+=1
    assert s.simplify(phi-1/s.Integer(2))!=0;count+=1
    # Existing orthogonal modal observation: handedness versus intensity.
    for b in (s.I,-s.I):
        assert s.Abs(b)**2+1==2;count+=1
        assert 2*s.im(b)/(1+s.Abs(b)**2) in (-1,1);count+=1
    print(f'{count} exact assertions PASS')
if __name__=='__main__':run()
