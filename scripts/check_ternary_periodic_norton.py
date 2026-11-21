"""Period-four nonlinear E/H/P source-backreaction fixtures on open 3^d grids.

Exact symbolic Norton signed-work identity + sparse periodic Newton solve.
Synthetic reference source V(t) with internal conductance; no physical Earth model.
"""
import numpy as np
import sympy as sp
from scipy.optimize import root_scalar
from scipy.sparse import csr_matrix, lil_matrix, identity, bmat
from scipy.sparse.linalg import lsmr
from check_ternary_stationary_cycle import incidence

EPS=.85; MU=.9; ETA=.35; A=4.; H=.11; G=.3; LOAD=.18
PERIOD=4


def symbolic_norton():
    dt,g,v,e,wload,relax,du=sp.symbols('dt g v e wload relax du', real=True)
    source_work=dt*e*g*(v-e)
    external=dt*g*v*e
    source_loss=dt*g*e**2
    assert sp.expand(source_work-external+source_loss)==0
    assert sp.expand((du-source_work+wload+relax)-(du-external+source_loss+wload+relax))==0
    return 2


def fixture(dim,beta,amplitude):
    B=np.asarray(incidence(dim),dtype=float)
    nv,ne=B.shape; N=2*nv+ne
    src=np.zeros(nv);src[0]=1.
    rec=np.zeros(nv);rec[-1]=1.
    V=.3+amplitude*np.array([0.,1.,0.,-1.])
    I=np.eye(nv);IH=np.eye(ne)
    ss=np.outer(src,src);rr=np.outer(rec,rec)
    # Initial point: an exact equilibrium for the mean voltage.
    e=G*.3/(G+LOAD)
    p=root_scalar(lambda z:A*z+beta*z**3-e,bracket=(0.,1.)).root
    rhs=LOAD*e*rec-G*(.3-e)*src
    h=np.linalg.lstsq(B,rhs,rcond=None)[0]
    eq=np.r_[np.full(nv,e),h,np.full(nv,p)]
    assert np.max(np.abs(B@h-rhs))<1e-11
    nodes=np.tile(eq,(PERIOD,1))
    def pair(x,y,k, jac=False):
        E0,H0,P0=np.split(x,[nv,nv+ne]);E1,H1,P1=np.split(y,[nv,nv+ne]);
        Em=(E0+E1)/2;Hm=(H0+H1)/2;dp=P1-P0
        jn=G*(V[k]-Em[0])*src
        rp=ETA*dp/H + A*(P0+P1)/2 + beta*(P0+P1)*(P0*P0+P1*P1)/4-Em
        r=np.r_[EPS*(E1-E0)+dp-H*(B@Hm+jn-LOAD*Em[-1]*rec),
                MU*(H1-H0)+H*B.T@Em,rp]
        if not jac: return r
        ker=H/2*(G*ss+LOAD*rr)
        j0=np.block([[-EPS*I+ker,-H/2*B,-I],
                     [H/2*B.T,-MU*IH,np.zeros((ne,nv))],
                     [-I/2,np.zeros((nv,ne)),np.diag(-ETA/H+A/2+beta/4*(P0*P0+P1*P1+2*P0*(P0+P1))) ]])
        j1=np.block([[EPS*I+ker,-H/2*B,I],
                     [H/2*B.T,MU*IH,np.zeros((ne,nv))],
                     [-I/2,np.zeros((nv,ne)),np.diag(ETA/H+A/2+beta/4*(P0*P0+P1*P1+2*P1*(P0+P1))) ]])
        return r,j0,j1
    def residual(arr,with_jac=False):
        seq=arr.reshape((PERIOD,N))
        pieces=[]
        blocks=[[None]*PERIOD for _ in range(PERIOD)]
        for k in range(PERIOD):
            nxt=(k+1)%PERIOD
            if with_jac:
                rr,j0,j1=pair(seq[k],seq[nxt],k,True)
                blocks[k][k]=csr_matrix(j0);blocks[k][nxt]=csr_matrix(j1)
            else: rr=pair(seq[k],seq[nxt],k)
            pieces.append(rr)
        if with_jac: return np.concatenate(pieces),bmat(blocks,format='csr')
        return np.concatenate(pieces)
    for iteration in range(16):
        r,j=residual(nodes.ravel(),True)
        if np.max(np.abs(r))<1e-11:break
        delta=lsmr(j,-r,atol=1e-13,btol=1e-13,maxiter=3000)[0].reshape(nodes.shape)
        step=1.
        while step>1/64 and np.max(np.abs(residual((nodes+step*delta).ravel())))>np.max(np.abs(r)):
            step/=2
        nodes+=step*delta
    res=float(np.max(np.abs(residual(nodes.ravel()))))
    assert res<1e-10,(dim,beta,amplitude,res)
    assert np.max(np.linalg.norm(np.diff(np.vstack([nodes,nodes[0]]),axis=0),axis=1))>1e-5 if amplitude else True
    works=np.zeros(5) # voltage-source supply, source resistor, load, dielectric relaxation, storage change
    for k in range(PERIOD):
        E0,H0,P0=np.split(nodes[k],[nv,nv+ne]);E1,H1,P1=np.split(nodes[(k+1)%PERIOD],[nv,nv+ne]);Em=(E0+E1)/2
        Pm=(P0+P1)/2
        stored=lambda E,HH,P:(EPS*np.dot(E,E)+MU*np.dot(HH,HH)+A*np.dot(P,P))/2+beta*np.sum(P**4)/4
        ext=H*G*V[k]*Em[0]
        src_loss=H*G*Em[0]**2
        useful=H*LOAD*Em[-1]**2
        relaxation=ETA*np.sum((P1-P0)**2)/H
        du=stored(E1,H1,P1)-stored(E0,H0,P0)
        assert abs(du-ext+src_loss+useful+relaxation)<1e-10
        works+=np.array([ext,src_loss,useful,relaxation,du])
    assert abs(works[4])<1e-10
    assert abs(works[0]-works[1]-works[2]-works[3])<1e-10
    if amplitude:
        assert np.max(np.ptp(nodes[:,:nv],axis=0))>1e-6
        assert np.max(np.ptp(nodes[:,nv:nv+ne],axis=0))>1e-7
        assert np.max(np.ptp(nodes[:,nv+ne:],axis=0))>1e-7
    assert works[0]>0 and works[1]>=0 and works[2]>0 and works[3]>=0
    return dict(dim=dim,beta=beta,amplitude=amplitude,residual=res,source_input=works[0],source_loss=works[1],load=works[2],relaxation=works[3],storage_change=works[4],state_span=float(np.max(np.ptp(nodes,axis=0))))


def run():
    checks=symbolic_norton()
    for dim in (2,3):
        for beta in (0.,.45):
            for amp in (0.,.12):
                out=fixture(dim,beta,amp)
                print(out)
                checks+=5
    print(f'{checks}/{checks} PASS (2 symbolic Norton identities; 8 periodic fixtures x 5 controls); SymPy {sp.__version__}')


if __name__=='__main__':run()
