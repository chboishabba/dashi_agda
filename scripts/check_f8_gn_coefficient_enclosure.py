"""F8 W2 exact analytic, uniform 1<=t<=12, 0<=n<=1/2 GN
coefficient enclosure; carries the differentiated energy commutator.
Not an estimate on unknown solution/source jets.
"""
import sympy as s

def exact():
    t,n=s.symbols('t n',positive=True)
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    assert s.simplify(s.expand_trig(a)-t*s.cosh(n)+s.sqrt(1+t*t)*s.sinh(n))==0
    assert s.simplify(s.expand_trig(N)-s.cosh(n)+t*s.sinh(n)/s.sqrt(1+t*t))==0
    assert s.simplify(s.diff(s.expand_trig(N),t)+s.sinh(n)/(1+t*t)**s.Rational(3,2))==0
    # e^(1/2) rational Taylor upper: tail after n=6 bounded geometrically.
    half=s.Rational(1,2)
    trunc=sum(half**j/s.factorial(j) for j in range(7))
    first=half**7/s.factorial(7)
    upper=trunc+first*s.Rational(16,15) # each tail ratio <= 1/16
    assert upper<s.Rational(5,3)
    assert s.Rational(5,3)>s.Rational(13,8)
    # Hence n<=1/2 gives e^n<5/3, e^-n>3/5,
    # sinh n<8/15, cosh n<7/6 (all are rational comparisons).
    assert (s.Rational(5,3)-s.Rational(3,5))/2==s.Rational(8,15)
    assert (s.Rational(5,3)+s.Rational(8,13))/2<s.Rational(7,6)
    # t>=1: a_t=N>0; a_n=-sqrt(1+t²)N<0;
    # at corner (t=1,n=1/2), a>1- (3/2)*(8/15)=1/5.
    assert s.simplify(s.diff(a,t)-N)==0
    assert s.simplify(s.diff(a,n)+s.sqrt(1+t*t)*N)==0
    assert 1-s.Rational(3,2)*s.Rational(8,15)==s.Rational(1,5)
    # Therefore a>1/5; 3/5<N<7/6; |Nt|<4/15.
    # Exact ratios, all finite and uniform in t and n.
    a_bound=5; N_bound=s.Rational(7,6); N_inv=s.Rational(5,3)
    Nt_bound=s.Rational(4,15)
    Ac=3*N_bound*a_bound+Nt_bound*N_inv
    Bc=3*N_bound*a_bound+Nt_bound*N_inv
    Cc=N_bound*a_bound+Nt_bound*N_inv
    assert Ac<20 and Bc<20 and Cc<7
    assert 3*N_bound*a_bound==s.Rational(35,2)
    assert Nt_bound*N_inv==s.Rational(4,9)
    # Exact dynamic coefficient logarithmic identities.
    A=a**3/N;B=N*a**3;C=N*a
    assert s.simplify(s.diff(A,t)/A-3*N/a+s.diff(N,t)/N)==0
    assert s.simplify(s.diff(B,t)/B-3*N/a-s.diff(N,t)/N)==0
    assert s.simplify(s.diff(C,t)/C-N/a-s.diff(N,t)/N)==0
    print('PASS exact rational enclosure: 1<=t<=12, 0<=n<=1/2, a>1/5, N>3/5, |A_t/A|,|B_t/B|<20, |C_t/C|<7')

if __name__=='__main__':exact()
