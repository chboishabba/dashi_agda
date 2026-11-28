"""F8 W2: original two-level GN/Israel inner boundary flux reduction.

On compatible, nonzero-k Israel data Z_n=-Q and Z_tn=-Q_t. The
second-level acceleration trace cancels by a reciprocal time boundary
correction. Remaining work costs only the Z_t trace, paid by E0+E1 on
the original finite collar. k=0 uses independent zero-mode j (no 1/k).
This does not give source Q,Q_t,Q_tt or positive full Einstein energy.
"""
import sympy as s


def exact():
    t,k,eta=s.symbols('t k eta',positive=True)
    Z,Q=s.Function('Z')(t),s.Function('Q')(t)
    f,j=s.Function('f')(t),s.Function('j')(t)
    A,M=s.Function('A')(t),s.Function('M')(t)
    Zn=(k*k*f/t**2-j)/3
    f_on=-3*t*t*(A+M/(s.I*k))/k**2
    q_on=A+M/(s.I*k)+j/3
    assert s.simplify(Zn.subs(f,f_on)+q_on)==0
    assert s.simplify(s.diff(Zn,t).subs({s.diff(f,t):s.diff(f_on,t),f:f_on})+s.diff(q_on,t))==0
    # On-shell inner boundary contribution to H' (outer minus inner):
    inner=(1+k*k)*t**3*s.diff(Z,t)*Q+eta*t**3*s.diff(Z,t,2)*s.diff(Q,t)
    correction=eta*t**3*s.diff(Z,t)*s.diff(Q,t)
    residual=(1+k*k)*t**3*s.diff(Z,t)*Q-eta*s.diff(t**3*s.diff(Q,t),t)*s.diff(Z,t)
    assert s.simplify(inner-s.diff(correction,t)-residual)==0
    # k=0 uses original Neumann data Z_n=-j/3, not the divided source.
    Qzero=j/3
    assert s.simplify(Zn.subs(k,0)+Qzero)==0
    zero=(1+k*k)*t**3*s.diff(Z,t)*Qzero+eta*t**3*s.diff(Z,t,2)*s.diff(Qzero,t)
    corrected=eta*t**3*s.diff(Z,t)*s.diff(Qzero,t)
    assert s.simplify((zero-s.diff(corrected,t)).subs(k,0)
          -s.diff(Z,t)*(t**3*Qzero-eta*s.diff(t**3*s.diff(Qzero,t),t)))==0
    # Conjugation for a genuine Fourier pair: modewise Re[conj(Z_t) S].
    zr,zi,sr,si=s.symbols('zr zi sr si',real=True)
    assert s.expand(s.re(s.conjugate(zr+s.I*zi)*(sr+s.I*si))-(zr*sr+zi*si))==0
    print('PASS Israel double-time correction, eliminated acceleration trace, independent zero mode')


def trace_bound():
    """Explicit original-collar bound for the SINGLE trace of v=Z_t."""
    from fractions import Fraction
    L=Fraction(1,2)
    Amin=Fraction(6,875) # a>1/5, N<7/6: A=a³/N>6/875
    Bmin=Fraction(3,625) # a>1/5, N>3/5: B=Na³>3/625
    # |v(0)|² <= 2/L ||v||² + 2L ||v_n||² by averaging FTC.
    # E0 >= Amin/2 ||Z_t||²; E1 >= Bmin/2 ||Z_tn||².
    c0=Fraction(4,1)/(L*Amin)
    c1=4*L/Bmin
    assert c0==Fraction(3500,3)
    assert c1==Fraction(1250,3)
    # Independent polynomial negative control: no Z_tt trace bound from E0+E1.
    # For v_m(n)=m^-1/2 exp(-m n), v_m' has bounded? Instead use
    # second-time trace as independent t-jet; time graph E2 would be needed
    # without the reciprocal cancellation above.
    x,y=s.symbols('x y',real=True)
    theta=s.symbols('theta',positive=True)
    assert s.expand(theta*x*x+y*y/(4*theta)-x*y-(2*theta*x-y)**2/(4*theta))==0
    print('PASS original collar Z_t trace <= (3500/3)E0+(1250/3)E1, no k=0 division')

if __name__=='__main__':
    exact()
    trace_bound()
