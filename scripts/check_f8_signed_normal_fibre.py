"""Exact signed F8 characteristic/constraint identities; no continuum claim."""
import sympy as s

def main():
    p,m,v,u,a,dy=s.symbols('P M v D_yU A dy', real=True)
    w=((1+v)*p+(1-v)*m)/2
    n=(p-m)/2
    g=((1+v)*p+(v-1)*m)/2
    q=n-u; i=g-a
    target=(2*a-(1+v)*p)/(v-1)
    checks=[p-w-(1-v)*n,m-w+(1+v)*n,g-v*w-(1-v*v)*n,
            i-(1-v*v)*q-v*w-(1-v*v)*u+a,
            (a+i-v*w)/(1-v*v)-n,
            (1-v)*(target-m)/dy-2*i/dy]
    for expr in checks: assert s.cancel(expr)==0
    t=s.symbols('t',positive=True)
    assert s.simplify(1/(1-1/(1+t*t))-(1+1/t**2))==0
    # A nonzero normal fibre can hide behind identical U and W.
    assert (w.subs({p:1-v,m:-(1+v)},simultaneous=True)).expand()==0
    assert s.expand(n.subs({p:1-v,m:-(1+v)},simultaneous=True))==1
    # Arbitrary derivative rows: the common forcing cancels exactly.
    dp,dm,f,sp,sm=s.symbols('DP DM F SP SM')
    assert s.expand(((1+v)*dp+f+sp-((v-1)*dm+f+sm))/2-((1+v)*dp+(1-v)*dm)/2-(sp-sm)/2)==0
    print('10/10 exact symbolic identities and collision controls PASS; continuum OPEN')
if __name__=='__main__': main()
