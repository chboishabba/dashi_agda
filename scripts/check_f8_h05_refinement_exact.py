"""Exact rational H05 transfers on nonnested original F8 grid spacings.
Cell-average source transfer and point-state transfer are different maps.
"""
import sympy as s
from itertools import permutations

def point(src,dst,degree=3):
    if len(src)<degree+1 or min(dst)<min(src) or max(dst)>max(src):
        raise ValueError('no extrapolation')
    rows=[]
    for x in dst:
        ids=sorted(sorted(range(len(src)),key=lambda i:abs(src[i]-x))[:degree+1])
        row=[s.S(0)]*len(src)
        for i in ids:
            row[i]=s.prod((x-src[j])/(src[i]-src[j]) for j in ids if j!=i)
        rows.append(row)
    return s.Matrix(rows)

def shell(src,dst,d):
    if src[0]!=dst[0] or src[-1]!=dst[-1]:raise ValueError('same clipped physical domain required')
    def vol(a,b):return (b**d-a**d)/d
    a=list(zip(src,src[1:]));b=list(zip(dst,dst[1:]))
    return s.Matrix([[vol(max(l,u),min(r,v))/vol(u,v) if max(l,u)<min(r,v) else 0
                      for l,r in a] for u,v in b])

def derivative(x):
    n=len(x);h=x[1]-x[0];D=s.zeros(n)
    D[0,0]=-1/h;D[0,1]=1/h;D[-1,-2]=-1/h;D[-1,-1]=1/h
    for i in range(1,n-1):D[i,i-1]=-1/(2*h);D[i,i+1]=1/(2*h)
    return D

def edges(h,L):
    return [s.S(0)]+[h*(i+s.Rational(1,2)) for i in range(int(L/h)+1) if h*(i+s.Rational(1,2))<L]+[L]

def main():
    count=0; collisions=0
    for hc,hf in [(s.Rational(12,1000),s.Rational(8,1000)),(s.Rational(8,1000),s.Rational(6,1000)),(s.Rational(16,1000),s.Rational(12,1000)),(s.Rational(12,1000),s.Rational(9,1000))]:
        L=hc*hf/s.gcd(hc,hf)*3
        c=[i*hc for i in range(int(L/hc)+1)];f=[i*hf for i in range(int(L/hf)+1)]
        S=point(c,f);T=point(f,c);Dc=derivative(c);Df=derivative(f)
        for j in range(4):
            assert S*s.Matrix([x**j for x in c])==s.Matrix([x**j for x in f]);count+=1
        U=s.Matrix([(-1)**i*(i+1) for i in range(len(c))]);R=U;J=-2*U;K=3*U;N=Dc*U+R+J+K
        assert S*N-Df*S*U==S*(R+J+K)+(S*Dc-Df*S)*U;count+=1
        assert T*S*U+(U-T*S*U)==U;count+=1
        for j in range(2):assert (S*Dc-Df*S)*s.Matrix([x**j for x in c])==s.zeros(len(f),1);count+=1
        assert S*Dc-Df*S!=s.zeros(len(f),len(c));collisions+=1
        for d in (3,7,11):
            a,b=edges(hc,L),edges(hf,L);V=s.Matrix([[(y**d-x**d)/d for x,y in zip(a,a[1:])]]);W=s.Matrix([[(y**d-x**d)/d for x,y in zip(b,b[1:])]])
            A=shell(a,b,d);B=shell(b,a,d)
            assert W*A==V;assert V*B==W;assert A*s.ones(len(a)-1,1)==s.ones(len(b)-1,1);count+=3
    print({'exact_checks':count,'nonzero_commutators':collisions})
if __name__=='__main__':main()
