"""BR267: inhomogeneous SAT from full-grid gauge trace; not an independent exterior solution."""
import inspect
import numpy as np
import check_hopf369_br266_sbp as sbp

def run():
    src=inspect.getsource(sbp.run)
    src=src.replace('correction=-jn-z*u[p]', 'correction=-jn-z*u[p]')
    # Modify the generated donor source before execution, keeping GMRES linear.
    marker="    src+='    print(\"BR266 SBP/SAT boundary work\",boundary_total,flush=True)\\n'"
    assert marker in src
    extra='''    src=src.replace('        T=h[', "        refu=h['DC'][sl][...,0,:]; refw=h['DC'][sl][...,1:4,:]; refj=B[..., :,None]*refu[...,None,:]+np.einsum('...ij,...jm->...im',D,refw)\\n        T=h[")
    src=src.replace('def sat(u,j,A,B,D):','def sat(u,j,A,B,D,incoming=False):')
    src=src.replace('correction=-jn-z*u[p]', 'correction=-jn-z*u[p]\\n                data=sign*refj[p][...,i,:]+z*refu[p] if incoming else np.zeros_like(jn)\\n                correction+=data')
    src=src.replace('net-=np.sum(face*z*u[p]**2)', 'net+=np.sum(face*(u[p]*data-z*u[p]**2))')
    src=src.replace('new,info=gmres', 'b+=dt*pack(np.zeros(shape),sat(np.zeros(shape),np.zeros(shape[:-1]+(3,5)),A,B,D,True)[0])\\n        new,info=gmres')
    src=src.replace('penalty,flux,net=sat(u,j,A,B,D)', 'penalty,flux,net=sat(u,j,A,B,D,True)')
    src=src.replace(' and net<=0','')
'''
    src=src.replace(marker,extra+marker)
    ns=dict(vars(sbp));exec(src,ns);ns['run']()

if __name__=='__main__':run()
