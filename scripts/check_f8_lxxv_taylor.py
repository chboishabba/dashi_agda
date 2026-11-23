"""Source-specific adapter to Bishop positive composition majorant."""
from fractions import Fraction as F
from math import ceil, factorial, comb
from check_f8_lxxii_rational_load import expneg, mul, POLY, SCALE

def conv(a,b,N):
    return [sum((a[j]*b[i-j] for j in range(max(0,i-len(b)+1),min(i+1,len(a)))),F(0)) for i in range(min(N+1,len(a)+len(b)-1))]

def power(a,k,N):
    p=[F(1)]
    for _ in range(k): p=conv(p,a,N)
    return p

def panel(x,y,a,b,q,N):
    c=(x+y)/2; R=(1-c)/2; r=(y-x)/(2*R)
    assert r<=F(1,4)
    A=[1/(1-c*c)]; al=2*c*R*A[0]; be=R*R*A[0]
    for n in range(1,N+1): A.append(al*A[-1]+(be*A[-2] if n>1 else 0))
    E=[F(1)]
    for n in range(1,N+1): E.append(-sum(j*A[j]*E[n-j] for j in range(1,n+1))/n)
    u=[c,R]; u2=power(u,2,N); P=[F(0)]
    for p in POLY[q]:
        P=conv(P,u2,N); P[0]+=p
    base=conv(conv(power(A,8,N),E,N),conv(P,power(u,2+4*q,N),N),N)
    den=b*b-a*a; right=u2.copy();right[0]-=a*a;right=[v/den for v in right];left=[-v for v in right];left[0]+=1
    pref=expneg(A[0]-1)
    # s=1/2 majorant. Include e^(1-A0) in majorant to avoid endpoint blowup.
    s=F(1,2); z=c+R*s; As=1/(1-z*z); exponent=1+As-2*A[0]
    if exponent<=0: Mexp=expneg(-exponent)[1]
    else: Mexp=1/expneg(exponent)[0]
    M= SCALE[q]*As**8*Mexp*z**(2+4*q)*sum(abs(p)*z**(2*(len(POLY[q])-1-i)) for i,p in enumerate(POLY[q]))
    out=[]
    for hat in (left,right):
        g=conv(base,hat,N); I=SCALE[q]*(y-x)*sum(g[k]*r**k/(k+1) for k in range(0,len(g),2))
        lo,hi=mul((I,I),pref)
        err=(y-x)*M*sum(abs(v)*s**i for i,v in enumerate(hat))*(r/s)**(N+1)
        out.append((lo-err,hi+err))
    return out

def enclose(h,N=20):
    n=ceil(1/h);cut=F(99,100);out=[[[F(0),F(0)] for _ in range(n+1)] for q in range(3)]
    for j in range(n):
        a,b=j*h,(j+1)*h; c=min(b,cut); stack=[(a,c)] if c>a else []
        while stack:
            x,y=stack.pop(); mid=(x+y)/2
            if (y-x)/(1-mid)>F(1,8): stack.extend([(x,mid),(mid,y)]);continue
            for q in range(3):
                for i,(lo,hi) in enumerate(panel(x,y,a,b,q,N),j):out[q][i][0]+=lo;out[q][i][1]+=hi
        length=max(F(0),min(b,F(1))-max(a,cut))
        for q in range(3):
            err=3*SCALE[q]*sum(map(abs,POLY[q]))*factorial(50)*F(1,50)**42*length
            for i in (j,j+1):out[q][i][0]-=err;out[q][i][1]+=err
    return out

def main():
    import numpy as np
    from ksw668_f8_weak_source import weak_source
    for h in (F(1,5),F(3,20)):
        bounds=enclose(h); n=ceil(1/h);r=np.arange(n+2)*float(h)*.04;src=weak_source(.04,r,float(h)*.04)
        for q in range(3):
            widths=[]
            for i,(lo,hi) in enumerate(bounds[q]):
                d=3+4*q; W=((i*h+h/2)**d-max(F(0),i*h-h/2)**d)/d
                val=F(float(src[q,i]))*W
                assert lo<=val<=hi,(h,q,i,float(lo-val),float(hi-val))
                widths.append(float(hi-lo))
            print(h,2*q,max(widths),flush=True)
if __name__=='__main__':main()
