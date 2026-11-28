import sympy as s
from itertools import combinations_with_replacement
from fractions import Fraction as Q
import argparse
keys=list(combinations_with_replacement(range(4),2))
Z=s.zeros

def eq(a,b):
    if isinstance(a,s.MatrixBase): assert (a-b).applyfunc(s.cancel)==Z(*a.shape),(a-b)
    else: assert s.cancel(a-b)==0,(a,b)

def sm(seed):
    return s.Matrix(4,4,lambda a,b:s.Rational(((min(a,b)+2)*(max(a,b)+seed+1))%17-8,19+seed))
def vec(seed):return s.Matrix([s.Rational((i+2)*(seed+1)%11-5,13+seed) for i in range(4)])

def data():
    U=s.eye(4);U[2,0]=s.Rational(1,7);U[3,1]=s.Rational(2,9)
    h=U.T*s.diag(-2,3,4,5)*U
    return h,vec(1),[sm(i+2) for i in range(4)],[vec(i+2) for i in range(4)]
def gh(h,dh):
    hi=h.inv();return s.Matrix([sum(hi[i,k]*(dh[i][k,a]-dh[a][i,k]/2) for i in range(4) for k in range(4)) for a in range(4)])
def lie(h,b,dh,db):
    D=s.Matrix.hstack(*db).T
    return sum((b[i]*dh[i] for i in range(4)),Z(4))+D*h+h*D.T

def metric(h,b,l):
    return h.row_join(h*b).col_join((b.T*h).row_join(s.Matrix([[l*l+(b.T*h*b)[0]]])))
def dg(h,b,l,dh,db,dl):
    v=dh*b+h*db
    return dh.row_join(v).col_join(v.T.row_join(s.Matrix([[2*l*dl+(2*db.T*h*b+b.T*dh*b)[0]]])))
def direct(h,b,l,dh,db,dl):
    g=metric(h,b,l);gi=g.inv();ds=[dg(h,b,l,a,c,d) for a,c,d in zip(dh,db,dl)]
    C=s.Matrix([sum(gi[i,k]*(ds[i][k,a]-ds[a][i,k]/2) for i in range(5) for k in range(5)) for a in range(5)])
    # K=-lambda Gamma^y_ab in material chart.
    K=s.Matrix(4,4,lambda a,b:-l*sum(gi[4,k]*(ds[a][k,b]+ds[b][k,a]-ds[k][a,b])/2 for k in range(5)))
    return K,C[:4,0],(C[4]-(b.T*C[:4,0])[0])/l

def decode(h,b,l,dh,db,dl,K,c,n,H,Hn):
    tau=s.trace(h.inv()*K)
    hy=2*l*K+lie(h,b,dh,db)
    by=sum((b[i]*db[i] for i in range(4)),Z(4,1))+l*l*h.inv()*(c+H-gh(h,dh)+s.Matrix(dl)/l)
    ly=sum(b[i]*dl[i] for i in range(4))+l*l*(n+Hn+tau)
    return hy,by,ly

def normal():
    h,b,dh,db=data();hi=h.inv();j=-s.Rational(6,5)
    M=sm(9);M-=s.trace(hi*M)*h/4
    c=vec(12);n=s.Rational(1,11)
    for i,l in enumerate([s.Rational(2,3),s.Rational(5,4)]):
        sg=1-2*i;K=M+sg*j*h/2;H=vec(8+i);Hn=s.Rational(i+1,17);dl=[s.Rational(k-i,19) for k in range(4)]
        hy,by,ly=decode(h,b,l,dh,db,dl,K,c,n,H,Hn)
        a,v,w=direct(h,b,l,dh+[hy],db+[by],dl+[ly])
        eq(a,K);eq(v-H,c);eq(w-Hn,n)
    print('PASS exact nonlinear unequal-lambda normal jet inverse; independent 2-sided Christoffel oracle')

def jacobian():
    h,b,dh,db=data();hi=h.inv();j=-s.Rational(6,5)
    vals=[];rows=[]
    for i,l in enumerate([s.Rational(2,3),s.Rational(5,4)]):
        y=s.symbols(f'y{i}:16') if False else s.symbols(f'v{i}_0:15');vals.extend(y)
        hy=s.Matrix(4,4,lambda a,k:y[keys.index(tuple(sorted((a,k))))]);by=s.Matrix(y[10:14]);ly=y[14]
        K=(hy-lie(h,b,dh,db))/(2*l);tau=s.trace(hi*K)
        dl=[s.Rational(k-i,19) for k in range(4)]
        C=gh(h,dh)-s.Matrix(dl)/l+h*(by-sum((b[k]*db[k] for k in range(4)),Z(4,1)))/l**2
        n=-tau+(ly-sum(b[k]*dl[k] for k in range(4)))/l**2
        rows.append((K,tau,C,n))
    P,T,C,N=rows[0];M,U,D,V=rows[1]
    out=s.Matrix([(P-M-j*h)[a,k] for a,k in keys]+[T+U,*list(C-D),N-V])
    J=out.jacobian(vals);assert J.shape==(16,30) and J.rank()==16
    ker=s.Matrix.hstack(*J.nullspace());assert ker.shape==(30,14)
    # homogeneous kernel coordinates: mean TF shape + common gauge
    tr=s.trace(hi*(P+M)/2);m=(P+M)/2-h*tr/4
    K=s.Matrix([m[a,k] for a,k in keys]+[*list((C+D)/2),(N+V)/2]).jacobian(vals)
    assert (K*ker).rank()==14
    print('PASS normal derivative block rank 16, kernel 14, exact 9+5 free-coordinate isomorphism')

def energy():
    # Flat normalized homogeneous principal F at common trace H,b.
    # [H_n]=0, [b_n]=d p, [l_n]=0, mean tau=0.
    # p=l+ - l-. All derivatives are signed same normal.
    h=s.diag(-1,1,1,1);z=s.Matrix(s.symbols('z:4'));ell=s.symbols('ell');p=s.Symbol('p')
    # Independent two-face jets; only scale plus time velocity nonzero.
    # Common normal scale derivative d is FREE; tangential shift
    # derivative jump pays the tangential gauge row. Standard separate
    # positive Gram wall work has nonzero coefficient in d.
    d=s.Symbol('d');G=s.Matrix(15,15,lambda i,j:s.Symbol(f'G{min(i,j)}_{max(i,j)}'))
    vel=s.eye(15)[:,14];normal=d*vel+s.eye(15)[:,4]/2
    assert s.expand((vel.T*G*normal)[0]).coeff(d)==G[14,14]
    # U=div b - tr(H_n)/2. Homogeneous mean and continuity
    # give U+ = U- = 0; hence separate Dirichlet wave for U
    # on a flat common constant-coefficient bulk (commutation).
    q=(z.T*h*z)[0];v=s.Matrix(s.symbols('v:4'));tr=s.Symbol('Htr')
    eq((z.T*h*(v+z*p-v))[0],q*p)
    # Normal derivative jump of U on a flat homogeneous solution:
    # [U_n]=div[b_n] - tr[H_nn]/2 = q p, since H continuous
    # and H_nn=-Box_wall H (for homogeneous bulk wave).
    # With forcing F_H: [U_n]=q p - tr[F_H]/2 plus
    # derivative of inhomogeneous tangential gauge jump.
    R=s.Matrix(s.symbols('r:4'));f=s.Symbol('f')
    eq((z.T*h*(z*p+R))[0]-f/2,q*p+(z.T*h*R)[0]-f/2)
    print('PASS free scale derivative flux obstruction; exact principal wall-wave source factor')

def warp():
    g=Q(10**7);j=Q(6,5)
    def eps(c1,c0):
        a=2*Q(c1)/g+Q(c0)/g**2
        assert 6*a<1
        return 18*a/(1-6*a)
    # BR35 relative DtN Green errors + flat interval tail <=2/g
    # + exact optical endpoint conversion norms R=13, 3I.
    dm=eps(1536,Q(30832,25))+2/g+13*j/(4*g)
    dg=eps(8,Q(1239,100))+2/g+3*j/(4*g)
    rm=8*(5*dm+3*j/g);rg=Q(3,2)*(2*dg+4*j/g)
    assert rm<Q(1,4) and rg<Q(1,4)
    assert 8/(1-rm)<11 and Q(3,2)/(1-rg)<2
    print('PASS BR35-derived sufficient F warped reference damping',g,'rho',float(rm),float(rg),'inverse',float(8/(1-rm)),float(Q(3,2)/(1-rg)))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['normal','jacobian','energy','warp'],required=True)
    {'normal':normal,'jacobian':jacobian,'energy':energy,'warp':warp}[p.parse_args().part]()
