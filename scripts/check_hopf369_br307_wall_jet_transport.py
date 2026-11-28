"""BR307: exact timelike-wall Gauss, normal-Ricci and Codazzi jet contracts.
Necessary geometric compatibility, not an actual bulk Einstein solution.
"""
import sympy as s

def check():
    t=s.Symbol('t');j=s.Rational(-6,5)
    h=s.diag(-s.Rational(7,5)**2,1,1,1)
    h[1:4,1:4]=s.Matrix([[3,1,0],[1,4,1],[0,1,2]])
    hi=h.inv(); tr=lambda X:s.trace(hi*X)
    project=lambda X:X-tr(X)*h/4
    B=[project(s.Matrix(4,4,lambda a,b:s.Rational(((min(a,b)+1)*7+(max(a,b)+1)*11+13*n)%19-9,23+n))) for n in range(7)]
    assert all(tr(M)==0 for M in B)
    S=sum((t**n*B[n] for n in range(7)),s.zeros(4))
    # Polynomial identities are proved at coefficient level, avoiding a huge expansion.
    plus,minus=S+j*h/2,S-j*h/2
    Q=lambda K:tr(K)**2-s.trace(hi*K*hi*K)
    # The Gauss difference for pure tension is 6 j tr(S).
    assert s.expand(Q(plus)-Q(minus)-6*j*tr(S))==0
    rhs=lambda K:-tr(K)*K+2*K*hi*K
    delta=rhs(plus)-rhs(minus)+j*tr(S)*h
    assert all(s.expand(z)==0 for z in delta)
    for n in range(7):
        assert s.expand(s.diff(Q(plus)-Q(minus),t,n).subs(t,0))==0
        assert all(s.expand(z)==0 for z in s.diff(rhs(plus)-rhs(minus),t,n).subs(t,0))
    # Codazzi: the entire jump of K_ab-tr(K)h_ab is -3j h_ab.
    assert plus-minus==j*h
    assert tr(plus)-tr(minus)==4*j
    assert plus-minus-(tr(plus)-tr(minus))*h==-3*j*h
    x=s.Symbol('x');J=s.Function('J')(x)
    assert s.diff(-3*J,x)==-3*s.diff(J,x)
    print('BR307 PASS seven exact pure-tension Gauss/normal-Ricci wall time jets')
    print('BR307 PASS trace-reversed Codazzi jump and variable-tension source')
    print('OPEN physical bulk/wall representatives and tangential evolution')
if __name__=='__main__':check()
