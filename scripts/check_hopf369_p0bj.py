"""BJ: actual coupled linearized barrier diagnostics, not interval validation."""
from check_hopf369_p0bh import *
import sympy as s

def weight(X,eps):
    delta=1-X[:3]@X[:3]
    al=1/j.sqrt(j.linalg.inv(metric(X.at[3].set(0.),eps))[3,3])
    return (1+(j.cosh(X[3]-L/2)/1.25-1)*al)*delta**2

def weight_jet(X,eps):
    fn=lambda X:weight(X,eps)
    return j.concatenate([j.atleast_1d(fn(X)),jax.grad(fn)(X),jax.hessian(fn)(X).ravel()])

Wfun=jax.jit(jax.vmap(weight_jet,(0,None)))

def reference():
    h,r,p=s.symbols('h r p',positive=True)
    d=1-r*r; v=d**p
    lap=h*h*d*d/4*(s.diff(v,r,2)+2/r*s.diff(v,r)+2*r/d*s.diff(v,r))
    assert s.simplify(lap/v-h*h*p*(-s.Rational(3,2)*d+(p-2)*r*r))==0
    b=s.symbols('b',positive=True)
    assert s.simplify(6*(b+3*(b*b-h*h)/b)-24*b+18*h*h/b)==0
    print('PASS exact AK barrier: -D R[b delta^2]/(b delta^2)=18 h0^2 (1+delta)/b^2 >= 11.52',flush=True)

def campaign(c):
    base=sample(10,456); q=sample(7,814)
    x=q[:,:3]/np.linalg.norm(q[:,:3],axis=1)[:,None]
    layers=np.vstack([np.c_[x*r,q[:,3]] for r in (.9,.99,.999,.9999)])
    y=sample(6,987)[:,:3]; seam=np.vstack([np.c_[y,np.zeros(len(y))],np.c_[y,np.full(len(y),L)]])
    X=np.vstack([base,layers,seam]); eps=.025
    def evaluate_sector(X,eps,c):
        rows=[]
        for i in range(0,len(X),128):
            x=X[i:i+128]; n=len(x); x=np.pad(x,((0,128-n),(0,0)),mode='edge')
            B,v=evaluate_points(x,eps,c); w=np.asarray(Wfun(j.array(x),eps)); psi=w[:,0]
            f=np.asarray(Rbatch(*B,v))/psi
            slopes=[]
            for t in (-.04,-.02,0.,.02,.04):
                D=np.asarray(DJ(*B,v+t*w)); slopes.append(-np.sum(D*w,axis=1)/psi)
            minus=np.asarray(Rbatch(*B,v-.04*w))/psi; plus=np.asarray(Rbatch(*B,v+.04*w))/psi
            rows.append(np.c_[f,*slopes,minus,plus][:n])
        return np.concatenate(rows)
    out=evaluate_sector(X,eps,c)
    for name,a in [('bulk',out[:1024]),('tail layers',out[1024:1536]),('endpoints',out[1536:])]:
        print(name,len(a),'weighted residual max',np.max(abs(a[:,0])),'min -D R psi/psi at shifts',np.min(a[:,1:6],axis=0),'barrier margins',np.min(a[:,6]),np.max(a[:,7]),flush=True)
    neg=c.copy();neg[:180].reshape(9,4,5)[:,:,[2,4]]*=-1;neg[180:]=c[180:].reshape(9,4,2)[:,:,::-1].ravel()
    Y=X[:128].copy();Y[:,3]=L-Y[:,3]
    reflected=evaluate_sector(Y,-eps,neg)
    print('signed replay weighted max discrepancy',np.max(abs(reflected-out[:128])),flush=True)
    Z=X[:128];zero=evaluate_sector(Z,0.,np.zeros_like(c));b=np.cosh(Z[:,3]-L/2)/1.25;delta=1-np.sum(Z[:,:3]**2,axis=1)
    target=18*h0*h0*(1+delta)/b**2
    print('zero reference slope max discrepancy',np.max(abs(zero[:,3]-target)),flush=True)
    assert np.max(abs(zero[:,3]-target))<1e-7 and np.max(abs(reflected-out[:128]))<1e-6
    print('all sampled slopes positive',bool(np.min(out[:,1:6])>0),'all sampled barriers bracket',bool(np.min(out[:,6])>=0 and np.max(out[:,7])<=0),flush=True)

if __name__=='__main__':
    reference(); c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));assert len(c)==252
    campaign(c)
