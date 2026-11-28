"""Conditional passive electromagnetic face realization and reverse work cap.
Local plane-wave witness, not global Whitney trace or atmospheric admission.
"""
import sympy as S

def face():
    a,b,Z,A,v=S.symbols('a b Z A v',real=True,positive=True)
    # sqrt(power) amplitudes normalized over original face area A.
    E=S.sqrt(Z/A)*(a+b)
    H=(a-b)/S.sqrt(Z*A)
    eps=1/(Z*v);mu=Z/v
    flux=S.simplify(A*E*H)
    density=S.simplify(A*(eps*E**2+mu*H**2)/2)
    assert S.expand(flux-a*a+b*b)==0
    assert S.expand(density-(a*a+b*b)/v)==0
    t,x=S.symbols('t x',real=True)
    f,g=S.Function('f'),S.Function('g')
    e=E.subs({a:f(t-x/v),b:g(t+x/v)})
    h=H.subs({a:f(t-x/v),b:g(t+x/v)})
    assert S.simplify(S.diff(e,x)+mu*S.diff(h,t))==0
    assert S.simplify(S.diff(h,x)+eps*S.diff(e,t))==0
    return dict(flux=flux,energy_per_length=density,E=E,H=H)

def budget(incident,controller,dark,loss,useful):
    I,C,D,L,Q=map(S.Rational,(incident,controller,dark,loss,useful))
    assert min(I,C,D,L,Q)>=0 and D<=I
    cap=I+C-D-L
    return dict(cap=cap,feasible=Q<=cap,shortfall=max(0,Q-cap),
                minimum_controller=max(0,Q+D+L-I))

def fixture():
    face()
    assert budget(1,0,S.Rational(16,25),0,1)['shortfall']==S.Rational(16,25)
    assert budget(1,0,0,0,1)['feasible']
    assert not budget(1,0,0,S.Rational(1,100),1)['feasible']
    print('PASS exact local Maxwell power waves and reverse energy cap')
if __name__=='__main__':fixture()
