"""SBP boundary flux and characteristic SAT on the BR262 metric history."""
import inspect
import numpy as np
import check_hopf369_br257_259_subsidiary_evolution as donor
from check_hopf369_br260_262_operator_weld import matched

def run():
    src=inspect.getsource(donor.run)
    start=src.index('    # Restricted');end=src.index('    def coeff',start)
    src=src[:start]+'''    m=shape[0]; H=np.ones(m);H[[0,-1]]=.5
    Q=np.zeros((m,m))
    for i in range(m-1):Q[i,i+1]=.5;Q[i+1,i]=-.5
    Q[0,0]=-.5;Q[-1,-1]=.5
    S=Q/H[:,None]/dx
    assert np.max(abs(dx*(H[:,None]*S+S.T*H[None,:])-np.diag([-1]+[0]*(m-2)+[1])))<1e-14
    W=H[:,None,None]*H[None,:,None]*H[None,None,:]; W=W[...,None]
    def der(q,i):return np.moveaxis(np.einsum('ij,j...->i...',S,np.moveaxis(q,i,0)),0,i)
    def grad(q):return np.stack([der(q,i) for i in range(3)],axis=-2)
    def div(q):return sum(der(q[...,i,:],i) for i in range(3))
    def sat(u,j,A,B,D):
        out=np.zeros_like(u); flux=0.; net=0.
        for i in range(3):
            for side,sign in ((0,-1),(-1,1)):
                p=[slice(None)]*3;p[i]=side;p=tuple(p)
                z=np.sqrt(A[p]*D[p][...,i,i]+B[p][...,i]**2)[...,None]
                # Homogeneous incoming impedance relation J_n=-z*u.
                jn=sign*j[p][...,i,:]; correction=-jn-z*u[p]
                out[p]+=correction/(dx*H[side])
                face=W[p]/H[side]*dx**2
                flux+=np.sum(face*u[p]*jn)
                net-=np.sum(face*z*u[p]**2)
        return out,flux,net
''' +src[end:]
    src=src.replace('np.sum(A[...,None]*u*u+np.einsum(\'...ij,...im,...jm->...m\',D,w,w)+q*q)','np.sum(W*(A[...,None]*u*u+np.einsum(\'...ij,...im,...jm->...m\',D,w,w)+q*q))')
    src=src.replace('return u,div(j)+lower,lower','return u,div(j)+lower+sat(u,j,A,B,D)[0],lower')
    src=src.replace('worst=0.;total=0.;','boundary_total=0.;worst=0.;total=0.;')
    src=src.replace('work=dt*dv*np.sum(u*(qm+lower-F))','''w=grad(qm);j=B[..., :,None]*u[...,None,:]+np.einsum('...ij,...jm->...im',D,w)
        penalty,flux,net=sat(u,j,A,B,D)
        assert abs(dv*np.sum(W*(u*div(j)+np.sum(grad(u)*j,axis=-2)))-flux)<1e-12
        assert abs(flux+dv*np.sum(W*u*penalty)-net)<1e-12 and net<=0
        boundary_total+=dt*net
        work=dt*(dv*np.sum(W*u*(qm+lower-F))+net)''')
    src+='    print("BR266 SBP/SAT boundary work",boundary_total,flush=True)\n'
    ns=dict(vars(donor),geometry=matched());exec(src,ns);ns['run'](11,8)

if __name__=='__main__':run()
