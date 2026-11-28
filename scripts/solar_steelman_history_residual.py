"""Rational method-of-steps error propagation, conditional on certified inputs."""
from fractions import Fraction as Q

def rational(x):
    if isinstance(x,float): raise TypeError('no floating bounds')
    return Q(x)

def exp_upper(x):
    x=rational(x)
    if x<=0: return 1/(1-x)
    n=max(1,2*x.numerator//x.denominator+1)
    return (1-x/n)**(-n)

def step(h,mu,b,c,residual,e0,e1,e2):
    h,mu,b,c,residual,e0,e1,e2=map(rational,(h,mu,b,c,residual,e0,e1,e2))
    assert h>0 and min(b,c,residual,e0,e1,e2)>=0
    f=b*e1+c*e2+residual
    end=exp_upper(mu*h)*e0+h*exp_upper(max(mu,0)*h)*f
    sup=exp_upper(max(mu,0)*h)*(e0+h*f)
    return end,sup

def replay(h,slabs,initial=0,history=(0,0)):
    # h must equal delay: each slab reads the preceding two slabs.
    e=rational(initial); past=list(map(rational,history)); out=[]
    assert len(past)==2 and min(e,*past)>=0
    for mu,b,c,residual in slabs:
        e,s=step(h,mu,b,c,residual,e,past[-1],past[-2])
        past.append(s);out.append((e,s))
    return out

def fixture():
    assert step(1,-1,0,0,0,1,0,0)==(Q(1,2),Q(1))
    assert replay(1,[(0,1,1,1),(0,1,1,0)])==[(Q(1),Q(1)),(Q(2),Q(2))]
    assert exp_upper(Q(1,2))==Q(16,9)
    print('PASS three exact propagation fixtures')
if __name__=='__main__':fixture()
