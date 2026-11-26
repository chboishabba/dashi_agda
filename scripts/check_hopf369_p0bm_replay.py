"""Independent post-selection replay of the pinned BM correction."""
from check_hopf369_p0bk_projection import *
from check_hopf369_p0bl_fit import bound
from fractions import Fraction as F

def run(c,cs,step):
    d=np.array(step['correction']);ds=np.array(step['projected_correction']);assert len(d)==len(ds)==252
    b=bound(d,ds,512,256)
    caps=(F(398,10**6),F(2749,10**6),F(2325,10**6));assert all(F(float(v))<cap for v,cap in zip(b,caps))
    eps=.025;X=sample(10,31415);x=sample(7,27182)[:,:3];Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    def evaluate(X):
        B,V=prepare(X,eps,4,2);q=trial(X,V@c,V@cs,2);a=trial(X,V@d,V@ds,2);psi=weight52(X,np.asarray(Wfun(j.array(X),eps)))[:,0]
        f=np.asarray(Rbatch(*B,q));g=np.asarray(Rbatch(*B,q+a));return B,q,a,f,g,psi
    rms=lambda x:float(np.sqrt(np.mean(x*x)))
    for label,Y in [('new bulk',X),('new seam',Z)]:
        B,q,a,f,g,p=evaluate(Y)
        print(label,len(Y),'before/after weighted RMS',rms(f/p),rms(g/p),'max',np.max(abs(f/p)),np.max(abs(g/p)),'before/after scalar RMS',rms(f),rms(g),flush=True)
        assert rms(g/p)<rms(f/p)
        if label=='new seam':
            j0=seam(B,q,len(Y)//2);j1=seam(B,q+a,len(Y)//2);print('new seam first/TF/scalar before',j0,'after',j1,flush=True);assert max(j1[:2])<1e-8
    # No other fit or line search on these samples.
    print('PASS pinned correction in global C1 tube and independent residual decrease',flush=True)
if __name__=='__main__':
    c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));cs=np.array(json.loads(Path(sys.argv[2]).read_text()));run(c,cs,json.loads(Path(sys.argv[3]).read_text()))
