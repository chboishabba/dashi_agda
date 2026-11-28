"""BR229 radial/Gaunt carrier, marked six-parameter linear inverse.
Uses the five exact radial integrals already checked by BR229.
"""
import sympy as s
from itertools import combinations
from functools import lru_cache
from sympy.physics.wigner import gaunt
Q=s.Rational
modes=[(l,m,spin) for l in (0,1) for m in range(-l,l+1) for spin in (-1,1)]
pairs=list(combinations(range(8),2))
@lru_cache(None)
def radial(a,c,b,d,k):
    u,v=sorted((tuple(sorted((a,c))),tuple(sorted((b,d)))))
    return Q({((0,0),(0,0),0):77,((0,0),(1,1),0):83,((0,1),(0,1),1):45,((1,1),(1,1),0):93,((1,1),(1,1),2):45}[u,v,k],512)
@lru_cache(None)
def eri(a,b,c,d):
    la,ma,sa=modes[a];lb,mb,sb=modes[b];lc,mc,sc=modes[c];ld,md,sd=modes[d]
    if sa!=sc or sb!=sd:return s.S.Zero
    out=0
    for k in range(3):
        if not(abs(la-lc)<=k<=la+lc and abs(lb-ld)<=k<=lb+ld):continue
        if (la+lc+k)%2 or (lb+ld+k)%2:continue
        for q in range(-k,k+1):
            g=gaunt(la,k,lc,-ma,-q,mc)*gaunt(lb,k,ld,-mb,q,md)
            if g:out+=4*s.pi*(-s.S.One)**(ma+mb+q)*g*radial(la,lc,lb,ld,k)/(2*k+1)
    return s.simplify(out)
def wedge(A):return s.Matrix(28,28,lambda i,j:A[pairs[i][0],pairs[j][0]]*A[pairs[i][1],pairs[j][1]]-A[pairs[i][0],pairs[j][1]]*A[pairs[i][1],pairs[j][0]])
def lift(A):
    t=s.Symbol('t');return wedge(s.eye(8)+t*A).diff(t).subs(t,0)
def run():
    V=s.Matrix(28,28,lambda i,j:eri(*pairs[i],*pairs[j])-eri(*pairs[i],*pairs[j][::-1]));assert V==V.T
    I=s.eye(3);zz=I[:,2];sig=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
    a,c,es,ep,ls,scale=s.symbols('a c es ep ls scale',real=True);H=s.zeros(8)
    for i in range(3):
        vv=zz.cross(I[:,i]);block=-s.I*a*sum((vv[k]*sig[k] for k in range(3)),s.zeros(2));H[:2,2+2*i:4+2*i]=block;H[2+2*i:4+2*i,:2]=block.H
        for j in range(3):
            vv=I[:,i]*zz[j]-I[:,j]*zz[i];H[2+2*i:4+2*i,2+2*j:4+2*j]=-s.I*c*sum((vv[k]*sig[k] for k in range(3)),s.zeros(2))
    L=[s.Matrix(3,3,lambda j,k:-s.I*s.LeviCivita(i,j,k)) for i in range(3)]
    H+=s.diag(es,es,*([ep]*6))+ls*s.diag(s.zeros(2),sum((s.kronecker_product(L[i],sig[i]/2) for i in range(3)),s.zeros(6)))
    E=s.zeros(8);orb={-1:s.Matrix([1,-s.I,0])/s.sqrt(2),0:zz,1:-s.Matrix([1,s.I,0])/s.sqrt(2)}
    for j,(l,m,spin) in enumerate(modes):
        z=0 if spin==1 else 1
        if l==0:E[z,j]=1
        else:
            for i in range(3):E[2+2*i+z,j]=orb[m][i]
    W=wedge(E);V=(W*V*W.H).applyfunc(s.simplify);P=(a,c,es,ep,ls,scale);H2=lift(H)+scale*V
    D=s.Matrix(list(H2)).jacobian(P);G=(D.H*D).applyfunc(s.simplify)
    assert G.det()!=0
    left=G.inv()*D.H;assert (left*D).applyfunc(s.simplify)==s.eye(6)
    vals=s.Matrix([Q(-2,7),Q(3,11),Q(-1,3),Q(5,13),Q(-1,17),Q(7,19)])
    assert (left*(D*vals)).applyfunc(s.simplify)==vals
    # Exact rejection of an off-model matrix via residual, not a forced fit.
    e=s.eye(784)[:,1];assert (e-D*(left*e)).applyfunc(s.simplify)!=s.zeros(784,1)
    print('BR275 marked design rank',G.rank(),'Gram determinant',G.det(),'signed six-parameter inverse PASS')
if __name__=='__main__':run()
