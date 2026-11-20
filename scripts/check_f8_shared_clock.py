"""Native stage-incidence pullback/pushforward, two-step source-active diagnostic."""
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import stage,F
from ksw668_f8_fv_source_flux import exact_cell_averages
from warp_frame_attribution import project,metric,raise_dual,lower,native_reverse
from warp_native_geometric_receiver import receiver_bank
from warp_israel_affine import radial_source_at_receiver,offsets,forced_identity

def check(order):
    dr,dy,h,eps=.008,.012,.001,.04
    nr,ny=13,7; rx=.025; shape=(3,3,ny,nr)
    src=exact_cell_averages(eps,np.arange(nr)*dr,dr)
    ts=np.array([brentq(lambda t:F(t)-F(1)-.02-k*h/2,.5,3) for k in range(5)])
    b=1/ts; v=-1/np.sqrt(1+ts**2)
    cp=np.zeros((3,nr));cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
    inc=np.array([[0,2,1],[2,4,3]])
    def geo(k):return b[k],v[k]
    def W(k):return metric(ny,nr,dr,dy,b[k])
    def euler(x,k,f):
        out=np.empty_like(x);stage(*x,*out,dr,dy,*geo(k),f,src,cp,cm,order)
        return project(x+h*out)
    units=[euler(np.zeros(shape),k,1.) for k in range(5)]
    obs=receiver_bank(ts[2],rx,eps,dr,dy,h,v,1,nr,ny)
    dg=radial_source_at_receiver(src,1.,rx,eps,dr);assert np.all(dg!=0)
    direct=np.zeros((6,5,3));direct[:,2]=offsets(dg)
    rng=np.random.default_rng(1530+order);x0=project(rng.normal(size=shape)*1e-4)
    def pair(a,b):return np.sum(a*b,axis=(0,2,3))
    def forward(f):
        x=x0.copy();states=[x]
        for a,b0,c in inc:
            u=euler(x,a,f[a]);z=.75*x+.25*euler(u,b0,f[b0]);x=x/3+2*euler(z,c,f[c])/3;states.append(x)
        return np.array([sum(pair(o,x) for o,x in zip(ch,states)) for ch in obs])+f[2]*direct[:,2]
    stagegrad=np.zeros((6,2,3,3))
    for ch in range(6):
        p=project(obs[ch,2])
        for i in (1,0):
            ks=inc[i];k=2*i
            adj,dual=native_reverse(raise_dual(p,W(k+2)),W(k),W(k+2),dr,dy,h,tuple(geo(j) for j in ks),order)
            for j,(d,l) in enumerate(zip(dual,ks)):stagegrad[ch,i,j]=pair(d,units[l])
            p=lower(adj,W(k))+project(obs[ch,i])
    grad=direct.copy()
    for i in range(2):
        for j in range(3):grad[:,inc[i,j]]+=stagegrad[:,i,j]
    f=np.array([.013,-.021,.034,-.012,.018]);delta=.001
    fd=np.stack([(forward(f+delta*z)-forward(f-delta*z))/(2*delta) for z in np.eye(5)],axis=1)
    err=np.max(np.abs(fd-grad))/np.max(np.abs(grad));assert err<1e-10,err
    assert np.all(np.abs(direct[4,2])>0)
    assert np.linalg.norm(stagegrad[:,0,1])>0
    assert np.linalg.norm(stagegrad[:,1,0])>0
    err0,scale=forced_identity(forward(f),f[2]*dg,ts[2]);assert np.all(np.abs(err0)<=1e-10*np.maximum(1.,scale))
    print(order,'gradient relative max',err,'direct',dg,'forced residual',err0,flush=True)
if __name__=='__main__':
    for order in (3,4):check(order)
