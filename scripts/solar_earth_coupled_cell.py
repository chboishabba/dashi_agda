"""Energy-normalized local electric/current exchange for frozen Drude species.
A local Maxwell material stage, not a spatial solver or a measured source.
"""
import hashlib,json,sys
from pathlib import Path
import numpy as np
import sympy as s
from scipy.linalg import expm
from scipy.integrate import quad
from scipy.constants import elementary_charge as e,electron_mass as me,atomic_mass as u,epsilon_0
from solar_earth_retarded_current import cross,radar,rates,composition


def generator(D,nu,omega,b,eps,load=0.):
    D,nu,omega=map(lambda x:np.asarray(x,dtype=float),(D,nu,omega)); b=np.asarray(b,dtype=float)
    if D.ndim!=1 or D.shape!=nu.shape or D.shape!=omega.shape or not np.isfinite([*D,*nu,*omega,*b,eps,load]).all() or np.any(D<0) or np.any(nu<0) or eps<=0 or load<0 or b.shape!=(3,) or abs(b@b-1)>1e-12:
        raise ValueError('invalid material')
    active=np.flatnonzero(D>0); N=3*(len(active)+1); A=np.zeros((N,N)); I=np.eye(3); R=[]
    A[:3,:3]=-load/eps*I
    loss=np.zeros_like(A); loss[:3,:3]=load/eps*I; R.append(loss)
    for k,i in enumerate(active):
        sl=slice(3*(k+1),3*(k+2)); coupling=np.sqrt(D[i]/eps)
        A[:3,sl]=-coupling*I; A[sl,:3]=coupling*I; A[sl,sl]=-nu[i]*I-omega[i]*cross(b)
        loss=np.zeros_like(A); loss[sl,sl]=nu[i]*I; R.append(loss)
    return A,R,active


def maps(A,R,h):
    """Return exp(hA) and independently integrated quadratic loss matrices.
    Small Van Loan blocks plus exact semigroup doubling avoid inverse-growth
    overflow at stiff steps; no eigenvector inversion or Hurwitz assumption.
    """
    if not np.isfinite(h) or h<0: raise ValueError('nonnegative finite time required')
    N=len(A); scale=h*np.linalg.norm(A,ord=np.inf)
    k=max(0,int(np.ceil(np.log2(scale)))+1) if scale>0 else 0
    dt=np.ldexp(h,-k); T=expm(dt*A); Q=[]
    for r in R:
        if not np.any(r): Q.append(np.zeros_like(A)); continue
        block=np.zeros((2*N,2*N)); block[:N,:N]=-A.T; block[:N,N:]=r; block[N:,N:]=A
        q=T.T@expm(dt*block)[:N,N:]; Q.append((q+q.T)/2)
    for _ in range(k):
        Q=[q+T.T@q@T for q in Q]; T=T@T
    return T,Q


def energy(z): return float(z@z/2)


def source_kick(z,impulse,eps):
    """Existing signed source-kick convention, applied in normalized coordinates."""
    out=z.copy(); out[:3]+=np.asarray(impulse)/np.sqrt(eps)
    work=float(np.asarray(impulse)@(z[:3]+out[:3])/(2*np.sqrt(eps)))
    return out,work


def fixtures():
    c,d,n,m,w,v,l=s.symbols('c d n m w v l',real=True); I=s.eye(3); Z=s.zeros(3); J=s.Matrix([[0,-1,0],[1,0,0],[0,0,0]])
    A=s.BlockMatrix([[-l*I,-c*I,-d*I],[c*I,-n*I-w*J,Z],[d*I,Z,-m*I-v*J]]).as_explicit()
    assert A+A.T==-2*s.diag(*([l]*3+[n]*3+[m]*3))
    z=s.Matrix(s.symbols('z:9',real=True)); assert s.expand(z.dot(A*z)+sum(q*t*t for q,t in zip([l]*3+[n]*3+[m]*3,z)))==0
    count=0; err=0.; qerr=0.; ledger=0.
    b=np.array([2.,-1.,2.])/3
    for D in ([0.,0.],[1.,0.],[1.,3.]):
        for nu in ([0.,0.],[.4,0.],[.4,1.2]):
            for load in (0.,.3):
                A,R,active=generator(D,nu,[-7.,11.],b,2.,load); z=np.linspace(-.7,1.,len(A))
                for h in (0.,.03,.8):
                    T,Q=maps(A,R,h); ref=expm(h*A); err=max(err,float(np.max(np.abs(T-ref))))
                    for r,q in zip(R,Q):
                        def f(t):
                            y=expm(t*A)@z; return y@r@y
                        expected=quad(f,0,h,epsabs=1e-11)[0]
                        qerr=max(qerr,abs(z@q@z-expected))
                    pre,wn=source_kick(z,[.1,-.2,.3],2.); mid=T@pre; post,wc=source_kick(mid,[-.2,.1,.4],2.)
                    ledger=max(ledger,abs(energy(post)-energy(z)+sum(pre@q@pre for q in Q)-wn-wc)); count+=1
    assert max(err,qerr,ledger)<1e-10
    # A free empty cell retains E, not a fictitious species current.
    A,R,active=generator([0],[0],[0],b,1); assert len(A)==3 and len(active)==0 and np.array_equal(maps(A,R,1)[0],np.eye(3))
    return dict(fixtures=count,propagator_error=err,independent_quadrature_error=qerr,signed_kick_ledger_error=ledger,symbolic_identities=2)


def replay(root,packet):
    raw=packet.read_bytes(); digest=hashlib.sha256(raw).hexdigest(); assert digest=='d771b81b3498e4cf9424325afe9e27f1c3f8125d0ba6c608c175cb62bd955fb6'
    rows=radar(root); model=[json.loads(x) for x in raw.splitlines()]; assert len(model)==len(rows)==3087
    for r,x in zip(rows,model): assert all(r[k]==x[k] for k in ('record','range_km','utc'))
    B=np.array([x['B_NED_T'] for x in model]); mag=np.linalg.norm(B,axis=1); b=B/mag[:,None]
    mass=np.array([me,30.5*u,16*u]); charge=e*np.array([-1,1,1]); pop=np.array([r['ne'] for r in rows])[:,None]*np.column_stack([np.ones(len(rows)),composition(root,rows)])
    D=pop*charge**2/mass; omega=mag[:,None]*charge/mass
    result={}; total=0
    for label in ('history','daily'):
        nu=rates(rows,np.array([x['neutral_'+label+'_SI'] for x in model])); out={}
        for h in (1e-6,1e-3):
            maxres=0.; minloss=0.; maxnorm=0.; maxsemi=0.
            for i in range(len(rows)):
                A,R,_=generator(D[i],nu[i],omega[i],b[i],epsilon_0)
                T,Q=maps(A,R,h); S=sum(Q); I=np.eye(len(A)); res=np.linalg.norm(T.T@T+2*S-I,ord=2)
                maxres=max(maxres,float(res)); minloss=min(minloss,*[float(np.linalg.eigvalsh(q)[0]) for q in Q]); maxnorm=max(maxnorm,float(np.linalg.norm(T,ord=2)))
                # Independent direct exponential on the same normalized generator.
                maxsemi=max(maxsemi,float(np.linalg.norm(T-expm(h*A),ord=2))); total+=1
            assert maxres<1e-8 and minloss>-1e-10 and maxnorm<1+1e-8 and maxsemi<1e-8
            out[str(h)]=dict(max_energy_operator_residual=maxres,min_loss_eigenvalue=minloss,max_propagator_norm=maxnorm,max_direct_expm_difference=maxsemi)
        result[label]=out
    return dict(packet_sha256=digest,rows=len(rows),operator_evaluations=total,diagnostic_steps_s=[1e-6,1e-3],histories=result)

if __name__=='__main__':
    result=fixtures(); result.update(replay(Path(sys.argv[1]),Path(sys.argv[2]))); result.update(status='CONDITIONAL_COUPLED_LOCAL_CELL',physical_admission=False,scope='Fixed population and coefficients, local electric-current exchange with no spatial curl in this stage; synthetic diagnostic timesteps and signed source-kick fixtures only. Loss operators independently integrated, no inferred actual work or physical propagation.')
    print(json.dumps(result,indent=2))
