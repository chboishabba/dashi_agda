"""Rational method-of-steps error propagation, conditional on certified inputs."""
from fractions import Fraction as Q

def rational(x):
    if isinstance(x,float): raise TypeError('no floating bounds')
    if hasattr(x,'as_numer_denom'):
        a,b=x.as_numer_denom()
        if not (a.is_Integer and b.is_Integer):raise TypeError('rational required')
        return Q(int(a),int(b))
    return Q(x)

def round_up(x,bits=64):
    x=rational(x);scale=1<<bits
    return Q(-(-x.numerator*scale//x.denominator),scale)

def exp_upper(x):
    x=rational(x)
    if x<=0: return 1/(1-x)
    # Scaling and squaring avoids an exponent proportional to x on a
    # huge rational denominator. Round UP on a dyadic grid after each step.
    k=0
    while x>Q(1,2):x/=2;k+=1
    term=total=Q(1)
    for j in range(1,17):term*=x/j;total+=term
    tail=term*x/17/(1-x/18)
    z=round_up(total+tail)
    for _ in range(k):z=round_up(z*z)
    return z

def step(h,mu,b,c,residual,e0,e1,e2):
    h,mu,b,c,residual,e0,e1,e2=map(rational,(h,mu,b,c,residual,e0,e1,e2))
    assert h>0 and min(b,c,residual,e0,e1,e2)>=0
    f=b*e1+c*e2+residual
    end=exp_upper(mu*h)*e0+h*exp_upper(max(mu,0)*h)*f
    sup=exp_upper(max(mu,0)*h)*(e0+h*f)
    return round_up(end),round_up(sup)

def replay(h,slabs,initial=0,history=(0,0)):
    # h must equal delay: each slab reads the preceding two slabs.
    # b,c include delayed ratio readback R for propagated state errors;
    # for initial ratio errors use max(1,||R||) in those coefficients.
    # residual includes approximate history and coefficient error.
    e=rational(initial); past=list(map(rational,history)); out=[]
    assert len(past)==2 and min(e,*past)>=0
    for mu,b,c,residual in slabs:
        e,s=step(h,mu,b,c,residual,e,past[-1],past[-2])
        past.append(s);out.append((e,s))
    return out

def fixture():
    assert step(1,-1,0,0,0,1,0,0)==(Q(1,2),Q(1))
    assert replay(1,[(0,1,1,1),(0,1,1,0)])==[(Q(1),Q(1)),(Q(2),Q(2))]
    assert Q(1648721270700128,10**15)<exp_upper(Q(1,2))<Q(1648721270700129,10**15)
    print('PASS three exact propagation fixtures')
if __name__=='__main__':fixture()
