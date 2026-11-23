"""Variable-period nonlinear E/H/P source-backreaction periodic fixtures on open 3^d grids.

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


def symbolic_norton():
    dt,g,v,e,wload,relax,du=sp.symbols('dt g v e wload relax du', real=True)
    source_work=dt*e*g*(v-e)
    external=dt*g*v*e
    source_loss=dt*g*e**2
    assert sp.expand(source_work-external+source_loss)==0
    assert sp.expand((du-source_work+wload+relax)-(du-external+source_loss+wload+relax))==0
    return 2


def fixture_period(dim,beta,amplitude,period,return_states=False):
    B=np.asarray(incidence(dim),dtype=float)
    nv,ne=B.shape; N=2*nv+ne
    src=np.zeros(nv);src[0]=1.
    rec=np.zeros(nv);rec[-1]=1.
    V=.3+amplitude*np.sin(2*np.pi*np.arange(period)/period)
    I=np.eye(nv);IH=np.eye(ne)
    ss=np.outer(src,src);rr=np.outer(rec,rec)
    # Initial point: an exact equilibrium for the mean voltage.
    e=G*.3/(G+LOAD)
    p=root_scalar(lambda z:A*z+beta*z**3-e,bracket=(0.,1.)).root
    rhs=LOAD*e*rec-G*(.3-e)*src
    h=np.linalg.lstsq(B,rhs,rcond=None)[0]
    eq=np.r_[np.full(nv,e),h,np.full(nv,p)]
    assert np.max(np.abs(B@h-rhs))<1e-11
    nodes=np.tile(eq,(period,1))
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
        seq=arr.reshape((period,N))
        pieces=[]
        blocks=[[None]*period for _ in range(period)]
        for k in range(period):
            nxt=(k+1)%period
            if with_jac:
                rr,j0,j1=pair(seq[k],seq[nxt],k,True)
                blocks[k][k]=csr_matrix(j0);blocks[k][nxt]=csr_matrix(j1)
            else: rr=pair(seq[k],seq[nxt],k)
            pieces.append(rr)
        if with_jac: return np.concatenate(pieces),bmat(blocks,format='csr')
        return np.concatenate(pieces)
    for iteration in range(25):
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
    for k in range(period):
        E0,H0,P0=np.split(nodes[k],[nv,nv+ne]);E1,H1,P1=np.split(nodes[(k+1)%period],[nv,nv+ne]);Em=(E0+E1)/2
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
    result=dict(dim=dim,beta=beta,amplitude=amplitude,residual=res,source_input=works[0],source_loss=works[1],load=works[2],relaxation=works[3],storage_change=works[4],state_span=float(np.max(np.ptp(nodes,axis=0))))
    if return_states: result["states"]=nodes.copy()
    return result



from check_ternary_frequency_sweep import harmonic

def main():
    checks=symbolic_norton()
    print('symbolic',checks)
    for dim in (2,3):
        for beta in (0.,.45):
            for period in (6,8,12):
                out=fixture_period(dim,beta,.12,period,return_states=True)
                nodes=out['states']; nv=3**dim; ne=incidence(dim).shape[1]
                mids=(nodes+np.roll(nodes,-1,axis=0))/2
                drive=.3+.12*np.sin(2*np.pi*np.arange(period)/period)
                vin=np.fft.fft(drive)[1]/period
                assert abs(vin)>.01;checks+=1
                near=np.fft.fft(mids[:,1])[1]/period/vin
                far=np.fft.fft(mids[:,nv-1])[1]/period/vin
                linear=harmonic(dim,beta,period,probe=1)
                assert abs(near-linear['near'])<(2e-7 if beta==0 else 7e-5),(dim,beta,period,near,linear['near']);checks+=1
                assert abs(far-linear['far'])<(2e-7 if beta==0 else 7e-5);checks+=1
                # second harmonic of polarization is a DC-bias nonlinear signature,
                # but the coefficient can be tiny; zero for the linear control.
                p2=np.fft.fft(mids[:,nv+ne])[2]/period
                assert np.isfinite(p2);checks+=1
                if beta==0:
                    assert abs(p2)<1e-12;checks+=1
                else:
                    assert abs(p2)>1e-11;checks+=1
                    # In the nonlinear DC-biased constitutive law the second
                    # harmonic is generated at quadratic order in drive amplitude.
                    half=fixture_period(dim,beta,.06,period,return_states=True)['states']
                    half_mid=(half+np.roll(half,-1,axis=0))/2
                    half_p2=np.fft.fft(half_mid[:,nv+ne])[2]/period
                    ratio=abs(p2/half_p2)
                    assert 3.5<ratio<4.5,(dim,period,ratio);checks+=1
                assert abs(out['storage_change'])<1e-10;checks+=1
                assert abs(out['source_input']-out['source_loss']-out['load']-out['relaxation'])<1e-10;checks+=1
                print(f'{dim}D beta={beta} N={period} near={near.real:+.8g}{near.imag:+.8g}j far={abs(far):.3g} |P2|={abs(p2):.3g} difference={abs(near-linear["near"]):.3g} err={out["residual"]:.2g}')
    print(f'{checks}/{checks} PASS full nonlinear period 6/8/12, SymPy {sp.__version__}')

if __name__=='__main__': main()
