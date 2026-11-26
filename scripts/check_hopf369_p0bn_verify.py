"""BN independent tests: exact radial jets and original coordinate metric."""
from fractions import Fraction as Q
import numpy as np
import sympy as s
from check_hopf369_p0bn import I,J,quotient,idx,zero
from check_hopf369_p0bn_radial import coefficients
from check_hopf369_p0bn_graph import build,eval_graph
from check_hopf369_p0an_metric import metric,L
from check_hopf369_p0bf import block_jets,evaluate
import jax
import jax.numpy as j

def points():
    # Exact rational source direction via tan(theta/2) in [0,1].
    return [(Q((i*7)%19+1,21),Q((i*5)%13,13),Q((i*3)%17,16)) for i in range(16)]

def point_data(pts):
    coeff=coefficients();out={}
    for key,(P,D) in coeff.items():
        vv=[Q(P.eval(r)/D.eval(r)) for r,_,_ in pts];out[str(key)]=np.array([[I.of(v).a,I.of(v).b] if not P.is_zero else [0.,0.] for v in vv])
    return out

def independent(X,eps,t):
    def w(X):
        d=1-X[:3]@X[:3];al=1/j.sqrt(j.linalg.inv(metric(X.at[3].set(0.),eps))[3,3]);b=j.cosh(X[3]-L/2)/1.25;return t*d*d*(1+(b-1)*al)
    q=j.concatenate([j.atleast_1d(w(X)),jax.grad(w)(X),jax.hessian(w)(X).ravel()]);res,*_=evaluate(*block_jets(X,eps),q)
    return res*t/w(X)


def exact_reference():
    b,h,d,t=s.symbols('b h d t',real=True,nonzero=True)
    w=t*b*d**2;lap=t*d**2*(4*b-3*h*h*(1+d)/b);grad2=t*t*d**4*(b*b-h*h+4*h*h*(1-d));R=6*(1+w)*lap-12*grad2-12*(1+w)**2+12
    assert s.cancel(R-(-18*h*h*t*d**2*(1+d)/b+h*h*t*t*d**4*(-54+30*d)))==0
    print('PASS exact reference barrier scalar identity',flush=True)

def replay():
    pts=points();data=point_data(pts);N=len(pts)
    def cols(vals):return np.array([[I.of(v).a,I.of(v).b] for v in vals])
    co=[(1-a*a)/(1+a*a) for _,a,_ in pts];si=[2*a/(1+a*a) for _,a,_ in pts]
    X=np.array([[float(r*z),0,float(r*c),float(y)*L] for (r,a,y),c,z in zip(pts,co,si)])
    # Explicit radial-source rotation check, plus direct axial interval evaluator.
    F=jax.jit(jax.vmap(independent,(0,None,None)))
    for t in (Q(-2,25),Q(2,25),Q(-1,25),Q(1,25)):
        g,keys=build(data,t);inputs=np.stack([cols([r for r,_,_ in pts]),cols([y for _,_,y in pts]),cols(co),cols(si)]+[data[k] for k in keys],axis=1);vals=eval_graph(*g,inputs)
        actual=np.asarray(F(j.array(X),.025,float(t)));neg=X.copy();neg[:,3]=L-neg[:,3];signed=np.asarray(F(j.array(neg),-.025,float(t)))
        # direct original source formula at the same physical points (interval AD).
        raw=quotient([I(X[:,0]),I(X[:,2]),I(np.array([float(y) for _,_,y in pts]))],I.of(t))
        mid=(vals[:,0]+vals[:,1])/2;diff=np.max(abs(mid-actual));rot=np.max(abs(mid-(raw.a+raw.b)/2));sign=np.max(abs(actual-signed));width=np.max(vals[:,1]-vals[:,0]);print('shift',t,'original BF error',diff,'axial rotation error',rot,'signed error',sign,'max point enclosure width',width,flush=True)
        assert np.all(np.isfinite(vals)) and diff<1e-8 and rot<1e-8 and sign<1e-8
    # Zero control uses actual original BF owner, not the radial graph.
    for t in (-.08,.08):
        actual=np.asarray(F(j.array(X),0.,t));b=np.cosh(X[:,3]-L/2)/1.25;d=1-np.sum(X[:,:3]**2,axis=1);target=-18*.64*t*(1+d)/b**2+.64*t*t*d*d*(-54+30*d)/b
        err=np.max(abs(actual-target));print('zero original BF error',err,flush=True);assert err<1e-8
    print('PASS radial rotation, factored interval evaluator, original BF and signed/zero controls',flush=True)
if __name__=='__main__':exact_reference();replay()
