"""KK block fourth-jet reduction and conditional receiver error bound.
Classical Schur/Routh/Grönwall; no certified Einstein lifespan asserted.
"""
import sympy as s


def eq(a,b=0):
    assert s.simplify(a-b)==0, (a,b)


def main():
    t=s.symbols('t'); q=s.symbols('q',positive=True)
    q2,q4,b,b2,b4,d,d2,d4=s.symbols('q2 q4 b b2 b4 d d2 d4',real=True)
    Q=q+q2*t**2/2+q4*t**4/24
    B=b+b2*t**2/2+b4*t**4/24
    D=d+d2*t**2/2+d4*t**4/24
    A=B/Q; g=D-B*B/Q; phi=s.sqrt(Q)
    A2=(b2-A.subs(t,0)*q2)/q
    A4=(b4-A.subs(t,0)*q4-6*A2*q2)/q
    p2=q2/(2*s.sqrt(q)); p4=(q4-6*p2*p2)/(2*s.sqrt(q))
    g4=d4-(q4*(b/q)**2+12*q2*(b/q)*A2+6*q*A2*A2+2*q*(b/q)*A4)
    for f,v in ((A,A4),(phi,p4),(g,g4)):
        eq(s.diff(f,t,4).subs(t,0),v)
    # Original G3 central H2 from P0V; H4 from numerical donor is
    # supplied as rounded diagnostic, not exact or interval data.
    e=s.Rational(1,4); p=s.Float('1.0580239940265903',30)
    a=2*e; ad=-32*e/p**2; pd=-112*e**2/(3*p)
    gd=-160*e**2/9; Q2=2*p*pd
    sub={q:p*p,b:p*p*a,d:p*p*(1+a*a),q2:Q2,b2:Q2*a+p*p*ad,d2:gd+Q2*a*a+2*p*p*a*ad,q4:s.Float('454.4687376'),b4:s.Float('641.7346330'),d4:s.Float('841.7712608')}
    print('central reduced fourth jets A,phi,g:',*[v.subs(sub).evalf(12) for v in (A4,p4,g4)])
    # Conditional Gronwall: E' = L E + delta; residual delta can
    # include both metric C1 error and numerical trajectory defect.
    L,delta,E0=s.symbols('L delta E0',positive=True)
    E=E0*s.exp(L*t)+delta*(s.exp(L*t)-1)/L
    eq(s.diff(E,t),L*E+delta);eq(E.subs(t,0),E0)
    eq(s.limit(E,L,0),E0+delta*t)
    print('PASS exact fourth-order KK reduction and conditional error envelope')


if __name__=='__main__':main()
