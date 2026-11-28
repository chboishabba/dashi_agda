"""BN: interval enclosure of axial, seam-preserving scalar barriers.
Exact coefficient constants; binary64 outward arithmetic (IEEE assumptions).
Bounds are only asserted on boxes that actually pass, never on samples.
"""
import numpy as np
from itertools import product
from fractions import Fraction
from math import factorial
from functools import lru_cache
import sys

# directed interval operations; no use of floating transcendental bounds
class I:
    def __init__(self,a,b=None):
        self.a=np.asarray(a,dtype=float);self.b=np.asarray(a if b is None else b,dtype=float)
    @staticmethod
    def of(x):
        if isinstance(x,I):return x
        if isinstance(x,Fraction):
            v=float(x);return I(np.nextafter(v,-np.inf),np.nextafter(v,np.inf))
        return I(x)
    def __add__(self,x):
        if isinstance(x,J):return NotImplemented
        x=I.of(x);return I(np.nextafter(self.a+x.a,-np.inf),np.nextafter(self.b+x.b,np.inf))
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,x):return self+-x if isinstance(x,(I,J)) else self+-I.of(x)
    def __rsub__(self,x):return -self+x
    def __mul__(self,x):
        if isinstance(x,J):return NotImplemented
        x=I.of(x);v=np.broadcast_arrays(self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b)
        return I(np.nextafter(np.minimum.reduce(v),-np.inf),np.nextafter(np.maximum.reduce(v),np.inf))
    __rmul__=__mul__
    def inv(self):
        if np.any((self.a<=0)&(self.b>=0)):raise ArithmeticError('denominator contains zero')
        return I(np.nextafter(1/self.b,-np.inf),np.nextafter(1/self.a,np.inf))
    def __truediv__(self,x):return self*I.of(x).inv()
    def __rtruediv__(self,x):return self.inv()*x
    def sqrt(self):
        if np.any(self.a<=0):raise ArithmeticError('sqrt interval')
        return I(np.nextafter(np.sqrt(self.a),-np.inf),np.nextafter(np.sqrt(self.b),np.inf))
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        if n==0:return I(1)
        if n==1:return self
        if n%2==0:
            lo=np.where((self.a<=0)&(self.b>=0),0,np.minimum(self.a*self.a,self.b*self.b));hi=np.maximum(self.a*self.a,self.b*self.b)
            return I(np.maximum(0,np.nextafter(lo,-np.inf)),np.nextafter(hi,np.inf))**(n//2) if n>2 else I(np.maximum(0,np.nextafter(lo,-np.inf)),np.nextafter(hi,np.inf))
        return self*(self**(n-1))

N=4
zero=(0,)*N
idx={k:sorted([a for a in product(range(k+1),repeat=N) if sum(a)<=k],key=lambda a:(sum(a),a)) for k in range(4)}
conv={a:[(b,tuple(x-y for x,y in zip(a,b))) for b in idx[sum(a)] if all(x>=y for x,y in zip(a,b))] for a in idx[3]}
# Taylor coefficients, not raw derivatives
class J:
    def __init__(self,x,k=3):self.k=k;self.d=x if isinstance(x,dict) else {zero:I.of(x)}
    def get(self,a):return self.d.get(a,I(0))
    def cut(self,k):return J({a:b for a,b in self.d.items() if sum(a)<=k},k)
    def __add__(self,x):
        if not isinstance(x,J):x=J(x,self.k)
        k=min(self.k,x.k);return J({a:self.get(a)+x.get(a) for a in self.d.keys()|x.d.keys() if sum(a)<=k},k)
    __radd__=__add__
    def __neg__(self):return J({a:-b for a,b in self.d.items()},self.k)
    def __sub__(self,x):return self+-x if isinstance(x,(I,J)) else self+-J(x,self.k)
    def __rsub__(self,x):return -self+x
    def __mul__(self,x):
        if not isinstance(x,J):return J({a:b*x for a,b in self.d.items()},self.k)
        k=min(self.k,x.k);return J({a:sum((self.d[b]*x.d[c] for b,c in conv[a] if b in self.d and c in x.d),I(0)) for a in idx[k] if any(b in self.d and c in x.d for b,c in conv[a])},k)
    __rmul__=__mul__
    def inv(self):
        z=self.get(zero).inv();d={zero:z}
        for a in idx[self.k][1:]:d[a]=-z*sum((self.d[b]*d[c] for b,c in conv[a] if b!=zero and b in self.d and c in d),I(0))
        return J(d,self.k)
    def sqrt(self):
        z=self.get(zero).sqrt();d={zero:z}
        for a in idx[self.k][1:]:d[a]=(self.get(a)-sum((d[b]*d[c] for b,c in conv[a] if b!=zero and c!=zero),I(0)))/(2*z)
        return J(d,self.k)
    def __truediv__(self,x):return self*(x.inv() if isinstance(x,J) else I.of(x).inv())
    def __rtruediv__(self,x):return self.inv()*x
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        if n==0:return J(1,self.k)
        if n==1:return self
        if n%2==0:
            z=self*self;z.d[zero]=self.get(zero)**2;return z**(n//2)
        return self*self**(n-1)
    def diff(self,i):
        return J({tuple(a[t]-(t==i) for t in range(N)):b*a[i] for a,b in self.d.items() if a[i]},self.k-1)
    @staticmethod
    def var(x,i,k=3):return J({zero:x,tuple(int(t==i) for t in range(N)):I(1)},k)

def sinhcosh(y):
    # y interval within [-1,1]; enclose Taylor tails by twice first omitted term.
    q=y.get(zero);assert np.all(q.a>=-1) and np.all(q.b<=1)
    ch=sum((q**(2*k)/factorial(2*k) for k in range(10)),I(0))+I(-1,1)*I.of(Fraction(2,factorial(20)))
    sh=sum((q**(2*k+1)/factorial(2*k+1) for k in range(9)),I(0))+I(-1,1)*I.of(Fraction(2,factorial(19)))
    # only y is variable, explicit Taylor derivative
    return J({(0,0,0,k):(ch if k%2==0 else sh)/factorial(k) for k in range(y.k+1)},y.k)

q=Fraction(1,3);v=4*sum(q**(2*k+1)/(2*k+1) for k in range(20));L=I(I.of(v).a,I.of(v+4*q**41/(41*(1-q*q))).b)
h=I.of(Fraction(4,5));j=I.of(Fraction(-6,5));eps=I.of(Fraction(1,40));
def mat(n,m,fn):return [[fn(i,k) for k in range(m)] for i in range(n)]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),0)

def quotient(box,shift,source=eps,source_jets=None):
    x=[J.var(box[0],0),J.var(I(0),1),J.var(box[1],2)];y=J.var(box[2]*L,3)
    r=sum(t*t for t in x);r.d[zero]=sum((t.get(zero)**2 for t in x),I(0));d=1-r;F=(2/h)*(1+r);D=d**4+F**2*r
    X=x;W=[2*F**2*x[0]*x[2]-2*F*d*d*x[1],2*F**2*x[1]*x[2]+2*F*d*d*x[0],d**4+F**2*(x[2]**2-x[0]**2-x[1]**2)]
    a=[source*h*(F*d*W[i]+(4*d/h+4*F)*x[i]*dot(x,W))/D**2 for i in range(3)] if source_jets is None else source_jets
    S=1+d**4*sum(t*t for t in a);al=1/S.sqrt();H=mat(3,3,lambda i,k:int(i==k)+d**4*a[i]*a[k]);Hi=mat(3,3,lambda i,k:int(i==k)-d**4*a[i]*a[k]/S)
    @lru_cache(None)
    def G(k,i,l):return h*(x[l]*int(k==i)-x[k]*int(i==l))
    T=mat(3,3,lambda i,k:h*d/2*a[k].diff(i)-sum(G(l,i,k)*a[l] for l in range(3))-2*h*x[i]*a[k])
    M=mat(3,3,lambda i,k:-al/2*(T[i][k]+T[k][i]-d**4*(a[i]*sum((T[k][l]-T[l][k])*a[l] for l in range(3))+a[k]*sum((T[i][l]-T[l][i])*a[l] for l in range(3)))))
    def tf(A):
        tr=sum(Hi[i][k]*A[i][k] for i in range(3) for k in range(3))/3
        return mat(3,3,lambda i,k:A[i][k]-tr*H[i][k])
    MT=tf(M);da=[h*d/2*al.diff(i) for i in range(3)];AA=tf(mat(3,3,lambda i,k:(da[i]*a[k]+da[k]*a[i])/2))
    C0=mat(3,3,lambda i,k:-j*AA[i][k]-j*al**2*(2-d**4*sum(t*t for t in a))*MT[i][k]/2)
    C1=mat(3,3,lambda i,k:-3*j*al**2*MT[i][k]/2)
    b=h*sinhcosh(y-L/2);bp=b.diff(3);warp=1+(b-1)*al;wh=shift*warp;u=1/(1+d*d*wh)
    f=y*y*(L-y)**2*(L-2*y)/L**3
    # Subtract the EXACT conformal reference barrier, not just AK.
    # f0-b=(1-b)*(1-alpha)=(1-b)*delta^4 |ahat|²/(root(root+1)).
    root=1/al;g0=mat(4,4,lambda i,k:(b*b if i<3 else J(1)) if i==k else J(0))
    ub=1/(1+d*d*shift*b)
    dwh=shift*(1-b)*d**4*sum(t*t for t in a)/(root*(root+1))
    A0=mat(4,4,lambda i,k:((b*b-1)*(-d*d*sum(t*t for t in a)/(root*(root+1))*int(i==k)+al*d*d*a[i]*a[k])+d*d*a[i]*a[k]+f*(C0[i][k]-d*d*u*wh*C1[i][k]) if i<3 and k<3 else (a[min(i,k)] if (i==3)!=(k==3) else J(0))))
    E=mat(4,4,lambda i,k:-(u+ub)*u*ub*dwh*g0[i][k]+u*u*A0[i][k])
    g=mat(4,4,lambda i,k:u*u*(g0[i][k]+d*d*A0[i][k]));g= [[z.cut(1) for z in row] for row in g]
    # Schur inverse via LDL, retaining interval differentiation.
    def inv3(A):
        # symmetric LDL (3x3)
        l10=A[1][0]/A[0][0];l20=A[2][0]/A[0][0];d1=A[1][1]-l10*A[1][0];l21=(A[2][1]-l20*A[1][0])/d1;d2=A[2][2]-l20*A[2][0]-l21*(A[2][1]-l20*A[1][0]);Li=[[1,0,0],[-l10,1,0],[l21*l10-l20,-l21,1]];di=[1/A[0][0],1/d1,1/d2]
        return mat(3,3,lambda i,k:sum(Li[l][i]*di[l]*Li[l][k] for l in range(3)))
    Q=mat(3,3,lambda i,k:g[i][k]-g[i][3]*g[3][k]/g[3][3]);Qi=inv3(Q);aa=[g[i][3]/g[3][3] for i in range(3)];A=[dot(row,aa) for row in Qi];Ig=mat(4,4,lambda i,k:Qi[i][k] if i<3 and k<3 else (-A[min(i,k)] if (i==3)!=(k==3) else 1/g[3][3]+dot(aa,A)))
    @lru_cache(None)
    def Gbase(k,i,l):
        if max(k,i,l)<3:return G(k,i,l)
        if k==3 and i<3 and l<3:return -b*bp*int(i==l)
        if k<3 and ((i==3 and l<3) or (l==3 and i<3)):return bp/b*int(k==min(i,l))
        return J(0)
    ell=[-h*t for t in x]+[J(0)];sc=[h*d/2]*3+[J(1)]
    p=[sc[i]*ub.diff(i)/ub for i in range(4)]
    gi=[1/(b*b)]*3+[J(1)]
    @lru_cache(None)
    def G0(k,i,l):return (Gbase(k,i,l)+int(k==i)*p[l]+int(k==l)*p[i]-g0[i][l]*gi[k]*p[k]).cut(1)
    def hess(i,k):return sc[i]*p[k].diff(i)-sum(Gbase(m,i,k)*p[m] for m in range(4))
    Hf=mat(4,4,hess);lap=sum(gi[i]*Hf[i][i] for i in range(4));norm=sum(gi[i]*p[i]*p[i] for i in range(4))
    Ricref=mat(4,4,lambda i,k:-3*g0[i][k]-2*Hf[i][k]+2*p[i]*p[k]-(lap+2*norm)*g0[i][k])
    Iref=[gi[i]/(ub*ub) for i in range(4)]
    E=[[z.cut(2) for z in row] for row in E]; E1=[[z.cut(1) for z in row] for row in E]
    U=[mat(4,4,lambda k,l:sc[i].cut(1)*E[k][l].diff(i)-sum(G0(m,i,k)*E1[m][l]+G0(m,i,l)*E1[k][m] for m in range(4))+2*ell[i].cut(1)*E1[k][l]) for i in range(4)]
    C=[mat(4,4,lambda i,k:sum(Ig[a][l]*(U[i][k][l]+U[k][i][l]-U[l][i][k]) for l in range(4))/2) for a in range(4)]
    # take values only once differentiating C; no further jets needed
    val=lambda z:z.get(zero) if isinstance(z,J) else I.of(z)
    cv=[[[val(z) for z in row] for row in cc] for cc in C];gv=[[[val(G0(k,i,l)) for l in range(4)] for i in range(4)] for k in range(4)];ev=list(map(val,ell));sv=list(map(val,sc));dv=val(d)
    def dc(a,i,k,l):return sv[l]*val(C[a][i][k].diff(l))+sum(gv[a][l][m]*cv[m][i][k]-gv[m][l][i]*cv[a][m][k]-gv[m][l][k]*cv[a][i][m] for m in range(4))
    R=mat(4,4,lambda i,k:sum(dc(a,i,k,a)-dc(a,i,a,k)+2*(ev[a]*cv[a][i][k]-ev[k]*cv[a][i][a])+dv**2*sum(cv[a][a][m]*cv[m][i][k]-cv[a][k][m]*cv[m][i][a] for m in range(4)) for a in range(4)))
    base=-18*h*h*shift*(1+dv)/(val(b)*val(warp))+h*h*shift**2*dv**2*(-54+30*dv)/val(warp)
    err=sum(val(Ig[i][k])*(R[i][k]-sum(val(E[k][l])*val(Iref[l])*val(Ricref[l][i]) for l in range(4))) for i in range(4) for k in range(4))/val(warp)
    return base+err

if __name__=='__main__':
    for e in (Fraction(0),Fraction(1,40)):
        for t in (Fraction(-1,25),Fraction(1,25)):
            q=quotient([I(.2),I(.1),I(.3)],I.of(t),I.of(e));print('point',e,t,q.a,q.b,flush=True)
