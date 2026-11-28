import sympy as s
from itertools import combinations_with_replacement
from check_hopf369_br_lorentz_row_transport import boost
eta=s.diag(-1,1,1,1,1); e=eta[:4,:4]; ids=list(combinations_with_replacement(range(5),2)); I=s.eye(15)
def enc(p):return s.Matrix([p[i,j] for i,j in ids])
def dec(v):return s.Matrix(5,5,lambda i,j:v[ids.index(tuple(sorted((i,j))))])
def op(f):return s.Matrix.hstack(*(enc(f(dec(I[:,i]))) for i in range(15)))
def ins(a,v):
    n=s.eye(5)[:,a];return n*v.T+v*n.T
def P(p):return s.Matrix([-2*p[a,4] for a in range(4)]+[s.trace(e*p[:4,:4])-4*p[4,4]])
def L(a,v):
    w=s.zeros(5,1);w[4]=-v[a];w[a]=eta[a,a]*v[4];return w
def Lt(a,p):
    C=s.Matrix.hstack(*(L(a,s.eye(5)[:,i]) for i in range(5)));return C*p+p*C.T
R=3*I+op(lambda p:ins(4,P(p)))
J=[op(lambda p,a=a:2*eta[a,a]*Lt(a,p)+ins(a,P(p))) for a in range(4)]
W=sum((eta[a,a]*op(lambda p,a=a:Lt(a,Lt(a,p)))+op(lambda p,a=a:ins(a,L(a,P(p)))) for a in range(4)),s.zeros(15))
C0=op(lambda p:2*(p-eta*s.trace(eta*p)))
Vbase=op(lambda p:s.Matrix(5,5,lambda i,j:(int(int(i)<4)+int(int(j)<4))*p[i,j]))
def baseA(a,p):
    tr=s.trace(e*p[:4,:4]);return s.Matrix([s.Rational(8,3)*p[i,a]-s.Rational(2,3)*eta[i,a]*tr for i in range(4)]+[2*p[4,a]])
Vbase+=sum((op(lambda p,a=a:ins(a,baseA(a,p))) for a in range(4)),s.zeros(15))
Lm=[s.Matrix.hstack(*(L(a,s.eye(5)[:,i]) for i in range(5))) for a in range(4)]
# Lie algebra generators: prove infinitesimal covariance for all six generators,
# then integrate on the connected complex Lorentz group.
count=0
for i,j in combinations_with_replacement(range(4),2):
    if i==j:continue
    A=s.zeros(5);A[i,j]=1;A[j,i]=-eta[i,i]*eta[j,j]
    G=op(lambda p:A*p+p*A.T)
    for M in (R,W,C0,Vbase):
        assert G*M-M*G==s.zeros(15);count+=1
    for b in range(4):
        assert G*J[b]-J[b]*G==sum((A[a,b]*J[a] for a in range(4)),s.zeros(15));count+=1
        K=[2*eta[a,a]*Lm[a] for a in range(4)]
        assert A*K[b]-K[b]*A==sum((A[a,b]*K[a] for a in range(4)),s.zeros(5));count+=1
print('PASS exact infinitesimal full operator identities',count)
# Independent endpoint jets, finite nontrivial rational complex chart.
def metric_side(p,px,z,k):
    H,b,l=p[:4,:4],p[:4,4],p[4,4]/2
    Hx,bx,lx=px[:4,:4],px[:4,4],px[4,4]/2
    tr=s.trace(e*H); div=(z.T*e*b)[0]
    return H,b,k*H+(Hx-z*b.T-b*z.T)/2-k*l*e,s.trace(e*Hx)/2-div-4*k*l,H*e*z-z*tr/2-z*l+bx+3*k*b,-s.trace(e*Hx)/2+div+lx

def gauge(p,px,m,mx,z,j):
    c,d=p[:4,0],m[:4,0];u,w=p[4],m[4]
    return u,c-d,px[:4,0]-mx[:4,0]+z*(u-w)-j*(c+d)/2,px[4]-mx[4]-(z.T*e*(c-d))[0]-2*j*(u+w)

p,px,m,mx=[dec(s.Matrix(s.symbols(f'{a}0:15'))) for a in ('p','v','m','w')]
c,cp,d,dp=[s.Matrix(s.symbols(f'{a}0:5')) for a in ('c','f','d','g')]
z=s.Matrix([s.Symbol('ell'),0,0,0]);k=s.Rational(3,5)
for w in (s.Matrix([s.I/2,s.I/3,0]),s.Matrix([s.Rational(1,4),s.I/5,s.Rational(1,6)])):
    r=w.dot(w); B=boost((1+r)/(1-r),2*w/(1-r)); A=s.diag(B,1);zz=B*z
    clean=lambda x:x.applyfunc(s.expand) if isinstance(x,s.MatrixBase) else s.expand(x)
    zero=lambda x:clean(x)==(s.zeros(*x.shape) if isinstance(x,s.MatrixBase) else 0)
    for pp,vv,kk in ((p,px,k),(m,mx,-k)):
        old=metric_side(pp,vv,z,kk); new=metric_side(A*pp*A.T,A*vv*A.T,zz,kk)
        expected=(B*old[0]*B.T,B*old[1],B*old[2]*B.T,old[3],B*old[4],old[5])
        assert all(zero(x-y) for x,y in zip(new,expected))
    old=gauge(c,cp,d,dp,z,2*k); new=gauge(A*c,A*cp,A*d,A*dp,zz,2*k)
    assert all(zero(x-y) for x,y in zip(new,(old[0],B*old[1],B*old[2],old[3])))
print('PASS two exact finite complex charts with independent metric and gauge endpoint jets')
