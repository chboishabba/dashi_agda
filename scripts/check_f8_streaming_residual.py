"""F8 W2/W4 adjacent-slab residual consumer; no certified floating quadrature.
Exact Bernstein convex-hull contract; sampled signed integrals are diagnostics.
"""
import hashlib,json,os
from pathlib import Path
import numpy as np
from math import comb,isqrt
from fractions import Fraction as Q

# Rows: power coefficients of the value/derivative Hermite basis.
H=np.array([[1,0,-3,2],[0,0,3,-2],[0,1,-2,1],[0,0,-1,1]],float).T

def derivative(c,axis,h):
    a=np.moveaxis(c,axis,0)
    return np.moveaxis(a[1:]*np.arange(1,len(a)).reshape((-1,)+(1,)*(a.ndim-1))/h,0,axis)

def bernstein(c):
    def mat(n):return np.array([[comb(i,j)/comb(n,j) if j<=i else 0 for j in range(n+1)] for i in range(n+1)])
    return np.einsum('ia,jb,ab...->ij...',mat(c.shape[0]-1),mat(c.shape[1]-1),c)

def hull(c):
    a=bernstein(c);return np.min(a,axis=(0,1)),np.max(a,axis=(0,1))

def jets(X,v,dy,cut=2):
    U,P,M=X[:3];W=((1+v)*P+(1-v)*M)/2;N=(P-M)/2
    D=np.gradient(W,dy,axis=0,edge_order=2)
    A=np.stack((U,W,N,D));A[:,-cut:]=0 # separate tapered reconstruction, not a state intervention
    return A

def slab(A,B,h,dy):
    # Shapes (jet,normal,mode), shared mixed jet W_y, both time faces.
    d=np.empty((4,4,A.shape[1]-1,A.shape[2]))
    for i,X in enumerate((A,B)):
        for j in range(2):
            sl=slice(j,j+d.shape[2]);d[i,j]=X[0,sl];d[i+2,j]=h*X[1,sl]
            d[i,j+2]=dy*X[2,sl];d[i+2,j+2]=h*dy*X[3,sl]
    return np.einsum('ia,jb,ab...->ij...',H,H,d)

def evaluate(c,x,y):
    return np.einsum('i,j,ij...->...',x**np.arange(c.shape[0]),y**np.arange(c.shape[1]),c)

def absmax(c):
    a,b=hull(c);return np.maximum(abs(a),abs(b))

def digest(x):return hashlib.sha256(np.ascontiguousarray(x).tobytes()).hexdigest()

def exact_majorant(A,B,h,dy,k2,box,source_abs,source_dt_abs):
    """Rational reference for one mode, all normal cells; supplied bounds are hypotheses.
    Inputs are exact rational values (floats interpreted as their exact binary values).
    Return L1_t L2_w(r), L1_t |g|, L1_t |g_T| upper bounds, no signed integral.
    """
    h,dy,k2=map(Q,(h,dy,k2));blo,vm,sm,am=map(Q,box)
    if min(h,dy,blo)<=0 or min(k2,vm,sm,am,Q(source_abs),Q(source_dt_abs))<0:raise ValueError('bounds')
    HH=H.astype(int);square=Q(0);gb=gtb=Q(0)
    def diff(c,axis,h):
        if axis==0:return [[Q(i)*x/h for x in c[i]] for i in range(1,len(c))]
        return [[Q(j)*row[j]/h for j in range(1,len(row))] for row in c]
    def maximum(c,wall=False):
        n,m=len(c)-1,len(c[0])-1
        return max(abs(sum(c[a][b]*Q(comb(i,a),comb(n,a))*Q(comb(j,b),comb(m,b)) for a in range(i+1) for b in range(j+1))) for i in range(n+1) for j in (range(1) if wall else range(m+1)))
    for cell in range(A.shape[1]-1):
        d=[[Q(0) for j in range(4)] for i in range(4)]
        for i,X in enumerate((A,B)):
            for j in range(2):
                d[i][j]=Q(X[0,cell+j]);d[i+2][j]=h*Q(X[1,cell+j])
                d[i][j+2]=dy*Q(X[2,cell+j]);d[i+2][j+2]=h*dy*Q(X[3,cell+j])
        c=[[sum(int(HH[i,a])*int(HH[j,b])*d[a][b] for a in range(4) for b in range(4)) for j in range(4)] for i in range(4)]
        ct,cy=diff(c,0,h),diff(c,1,dy);ctt,cty,cyy=diff(ct,0,h),diff(ct,1,dy),diff(cy,1,dy)
        z=blo+cell*dy
        m=maximum(ctt)+2*vm*maximum(cty)+sm*maximum(cyy)+(am+3/z)*maximum(cy)+k2*maximum(c)
        square+=dy*m*m/z**3
        if cell==0:
            W,N=maximum(ct,True),maximum(cy,True)
            gb=Q(source_abs)+vm*W+sm*N
            gtb=Q(source_dt_abs)+am*W+vm*maximum(ctt,True)+2*vm*am*N+sm*maximum(cty,True)
    # Exact rational upward square root (dyadic grid), no float rounding.
    scale=2**40;z=square*scale**2;root=isqrt(z.numerator//z.denominator)
    if Q(root*root)<z:root+=1
    return h*Q(root,scale),h*gb,h*gtb

class Ledger:
    # Row 0 signed integral wr, row 1 sampled L1_t L2_w(r), row 2
    # analytic convex-hull majorant (ordinary FP evaluation, NOT rounded out),
    # rows 3,4 signed/absolute wall discrepancy; row 5 sampled g_T L1.
    # rows 6,7 signed dual pairings, row 8 sampled dual residual L1_t L2_w.
    def __init__(self,n):self.a=np.zeros((9,n));self.cursor=0
    def add(self,A,B,T,h,dy,k,clock,source,clock_box,source_dt,dual=None):
        c=slab(A,B,h,dy);ct=derivative(c,0,h);cy=derivative(c,1,dy)
        ctt=derivative(ct,0,h);cty=derivative(ct,1,dy);cyy=derivative(cy,1,dy)
        # Clock box supplies lower b, upper |v|, upper s, upper |v_T|.
        blo,vm,sm,am=clock_box;yl=dy*np.arange(c.shape[2])[:,None];zlo=blo+yl
        # Convex-hull inequality exact over reals for all x,y in [0,1].
        m=absmax(ctt)+2*vm*absmax(cty)+sm*absmax(cyy)+(am+3/zlo)*absmax(cy)+k*k*absmax(c)
        self.a[2]+=h*np.sqrt(np.sum(dy*zlo**-3*m*m,axis=0))
        gx,gw=np.polynomial.legendre.leggauss(3);gx=(gx+1)/2;gw=gw/2
        for x,wx in zip(gx,gw):
            t=T+h*x;b,v,s,a=clock(t);square=0;dual_square=0
            for y,wy in zip(gx,gw):
                z=b+yl+dy*y;w=z**-3
                r=evaluate(ctt,x,y)-2*v*evaluate(cty,x,y)-s*evaluate(cyy,x,y)-(a-3/z)*evaluate(cy,x,y)+k*k*evaluate(c,x,y)
                self.a[0]+=h*wx*dy*wy*np.sum(w*r,axis=0)
                square+=dy*wy*np.sum(w*r*r,axis=0)
                if dual is not None:
                    phi,Lphi=dual(t,yl+dy*y)
                    self.a[6]+=h*wx*dy*wy*np.sum(w*phi*r,axis=0)
                    dual_square+=dy*wy*np.sum(w*Lphi*Lphi,axis=0)
            self.a[1]+=h*wx*np.sqrt(square)
            W=evaluate(ct,x,0)[0];N=evaluate(cy,x,0)[0]
            g=source(t)-v*W-s*N
            gt=source_dt(t)-a*W-v*evaluate(ctt,x,0)[0]+2*v*a*N-s*evaluate(cty,x,0)[0]
            self.a[3]+=h*wx*g;self.a[4]+=h*wx*abs(g);self.a[5]+=h*wx*abs(gt)
            if dual is not None:
                phi,_=dual(t,0.)
                self.a[7]+=h*wx*b**-3*phi*g;self.a[8]+=h*wx*np.sqrt(dual_square)
        self.cursor+=1
    def save(self,path,identity,X):
        p=Path(path);tmp=p.with_suffix('.tmp');meta=json.dumps(identity,sort_keys=True)
        with tmp.open('wb') as f:
            np.savez(f,identity=meta,cursor=self.cursor,X=X,ledger=self.a,xsha=digest(X),asha=digest(self.a));f.flush();os.fsync(f.fileno())
        os.replace(tmp,p)
    @classmethod
    def load(cls,path,identity):
        with np.load(path,allow_pickle=False) as z:
            if z['identity'].item()!=json.dumps(identity,sort_keys=True):raise ValueError('identity mismatch')
            X=z['X'];a=z['ledger'];cursor=int(z['cursor'])
            if digest(X)!=z['xsha'].item() or digest(a)!=z['asha'].item():raise ValueError('digest mismatch')
        if a.shape!=(9,X.shape[-1]) or cursor<0 or not np.isfinite(a).all() or not np.isfinite(X).all():raise ValueError('invalid checkpoint')
        obj=cls(X.shape[-1]);obj.a=a;obj.cursor=cursor;return obj,X

def check():
    # Independent polynomial with mixed jets, exact (up to roundoff) cubic reconstruction.
    h=.25;dy=.5;y=np.arange(4)*dy;k=np.array([1.,2.]);p=lambda t:np.stack([np.broadcast_to(1+t*t+y[:,None]**3+t*y[:,None],(4,2)),np.broadcast_to(2*t+y[:,None],(4,2)),np.broadcast_to(3*y[:,None]**2+t,(4,2)),np.ones((4,2))])
    A,B=p(0),p(h);c=slab(A,B,h,dy);checks=0
    for x in (0,.125,.5,.875,1):
        for j in (0,.3,1):
            Y=y[:-1,None]+dy*j;T=h*x;ref=1+T*T+Y**3+T*Y
            np.testing.assert_allclose(evaluate(c,x,j),np.broadcast_to(ref,(3,2)),atol=1e-13);checks+=1
            lo,hi=hull(c);a=evaluate(c,x,j);assert np.all(a>=lo-1e-14) and np.all(a<=hi+1e-14);checks+=1
    clock=lambda t:(2.,0.,1.,0.);src=lambda t:np.full(2,t)
    L=Ledger(2);L.add(A,B,0,h,dy,k,clock,src,(2.,0.,1.,0.),lambda t:np.ones(2))
    assert np.all(L.a[1]<=L.a[2]) and np.max(abs(L.a[3:6]))<1e-12;checks+=2
    for j in range(2):
        exact=exact_majorant(A[:,:,j],B[:,:,j],h,dy,k[j]**2,(2,0,1,0),h,1)
        assert float(exact[0])+1e-12>=L.a[2,j] and exact[1]>=0 and exact[2]>=0;checks+=1
    D=Ledger(2);D.add(A,B,0,h,dy,k,clock,src,(2.,0.,1.,0.),lambda t:np.ones(2),dual=lambda t,y:(1.,0.))
    np.testing.assert_allclose(D.a[6],D.a[0]);assert np.max(abs(D.a[7:]))<1e-12;checks+=2
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        pth=Path(tmp)/'checkpoint.npz';X=np.ones((6,4,2));L.save(pth,{'test':1},X);R,Z=Ledger.load(pth,{'test':1})
        assert R.cursor==1 and np.array_equal(R.a,L.a) and np.array_equal(Z,X);checks+=1
        try:Ledger.load(pth,{'test':2})
        except ValueError:checks+=1
        else:raise AssertionError('identity guard')
    return dict(checks=checks,sampled_norm=L.a[1].tolist(),hull_majorant=L.a[2].tolist(),scope='manufactured diagnostic; no interval rounding or original continuum certificate')

if __name__=='__main__':print(json.dumps(check(),indent=2))
