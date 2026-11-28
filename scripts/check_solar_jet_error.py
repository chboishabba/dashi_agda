"""Independent symbolic event valuations and original native two-jet residuals."""
import numpy as np
import sympy as S
from scipy.sparse import csr_matrix
from solar_jet_error import event_difference_coefficients,event_difference,event_error,receiver_error,residual_coefficients
from solar_physical_cone import timed_step

def run():
    s=S.symbols('s',positive=True)
    cases=[((4,1,2),(2,1,1),(1,2,0)),((0,4,1),(0,2,1),(0,3,2)),
        ((0,0,4),(0,0,2),(0,0,1)),((0,0,0),(0,0,0),(0,0,9)),
        ((4,2,3),(0,2,1),(0,0,3)),((4,2,3),(0,0,2),(0,0,1)),
        ((0,4,2),(0,1,0),(4,0,1)),((0,0,4),(0,0,2),(3,1,0)),
        ((0,4,2),(0,0,1),(0,0,2)),((4,0,0),(0,0,0),(2,0,0)),
        ((0,4,0),(0,0,2),(0,0,0))]
    poly=lambda t:sum(v*s**(2*k) for k,v in enumerate(t))
    jet=lambda z:S.expand(S.series(z,s,0,3).removeO())
    for n,f,a in cases:
        N,F,A=map(poly,(n,f,a));M=F+A;old=S.sqrt(N)*(2+3*s+5*s*s)
        new=F*(2+3*s+5*s*s)/S.sqrt(M)
        c,oo,no=event_difference_coefficients(np.array(n)[:,None],(np.array(n)-f)[:,None],np.array(a)[:,None])
        dx=np.tile([float(jet(old).coeff(s,k)) for k in range(3)],(3,1)).T
        out=event_difference(c,oo,no,dx)
        exact=np.tile([float(jet(new).coeff(s,k)) for k in range(3)],(3,1)).T
        assert np.allclose(out,exact,rtol=1e-12,atol=1e-12)
        radii=event_error(np.linalg.norm(dx,axis=1),np.max(abs(c[1])),np.max(abs(c[2])))
        assert np.all(np.linalg.norm(out,axis=1)<=radii+1e-12)
    try:event_difference(c,oo,no,np.ones((3,3)))
    except ValueError:pass
    else:raise AssertionError('uninhabited input admitted')
    # Original cone, heterogeneous site-local diagonal losses and signed exchange.
    mesh=dict(positions_m=[[0,0,0],[1,0,0],[2,0,0]],coordinate_site=[0,1,2],
        faces=[dict(id='a',source=0,target=1,normal=[1,0,0],area_m2=1),dict(id='b',source=1,target=2,normal=[1,0,0],area_m2=1)],front_speed_m_s=100.)
    H=np.diag([-.5,-.25,-.1]);A1=np.array([[0.,-1,0],[1,0,-2],[0,2,0.]])
    A2=np.array([[-.2,.5,0],[-.5,.1,-.3],[0,.3,-.2]])
    load=np.array([.2,.1,.05]);du=np.array([.1,-.1,.2]);h=.25;f=np.array([.1,0,0]);z=np.zeros(3)
    rng=np.random.default_rng(369);actual=rng.normal(size=(3,3));reference=rng.normal(size=(3,3))
    E=np.linalg.norm(actual-reference,axis=1);ratios=[];work_ratios=[]
    def work(m):return h*np.array([load@(m[0]**2),2*(load*m[0])@m[1],load@(m[1]**2)+2*(load*m[0])@m[2]+du@(m[0]**2)])
    for _ in range(4):
        def evolve(v,error=None):
            x,r=timed_step(v[0],csr_matrix(H),f,h,mesh,retain_local_midpoint=True,jvp=(v[1],csr_matrix(A1),z),
                atlas_pairs=((0,1),(1,2)),right_limit=csr_matrix(H),jet2=(v[2],csr_matrix(A2),z),jet_error_seed=error)
            out=np.array([x,r['state_jvp'],r['state_coefficient2']]);mid=np.array([r[k] for k in ('local_midpoint','local_midpoint_jvp','local_midpoint_coefficient2')]);return out,mid,r
        actual,am,_=evolve(actual);shadow,sm,r=evolve(reference,E)
        propagated=np.array(r['jet_endpoint_error_bound_candidate']);observed=np.linalg.norm(actual-shadow,axis=1)
        ratios.append(float(np.max(observed/propagated)))
        wr=receiver_error(sm,r['jet_local_midpoint_error_bound_candidate'],load,du,h)
        work_ratios.append(float(np.max(abs(work(am)-work(sm))/wr)))
        assert np.all(abs(work(am)-work(sm))<=wr+1e-12)
        reference=shadow+rng.normal(size=(3,3))*.1
        out=residual_coefficients(actual,shadow,reference,propagated);E=np.asarray(out['error_bound_candidate'])
    assert max(ratios)<=1+1e-12 and max(work_ratios)<=1+1e-12
    assert np.all(E>0)
    print(dict(status='TRIANGULAR_JET_ERROR_PASS',symbolic_event_cases=len(cases),native_steps=4,
        max_propagation_ratio=max(ratios),max_work_ratio=max(work_ratios),final_bounds=E.tolist(),physical_admission=False))
if __name__=='__main__':run()
