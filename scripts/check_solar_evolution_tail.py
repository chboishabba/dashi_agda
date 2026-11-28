"""Local storage, affine residual and changing-tail coefficient checks.
Independent small matrices; native spherical campaign is a separate gate.
"""
import numpy as np
import sympy as S
from scipy.sparse import csr_matrix
from solar_matrix_storage import matrix,finite,block,close,nonzero_pairs,diagonal
from solar_evolution_residual import event_affine,field_maps,coefficient_reopen,residual_step
from solar_changing_tail import tail_envelope,exact_uniform_block

def run():
    rng=np.random.default_rng(369)
    for d in (3,9,17):
        H=rng.normal(size=(d,d));H[abs(H)<1]=0
        A=matrix(csr_matrix(H));site=np.arange(d)//3;ix=np.arange(0,d,2)
        assert finite(A) and close(H,A,rtol=0,atol=0)
        assert np.array_equal(block(A,ix),block(H,ix))
        assert nonzero_pairs(H,site)==nonzero_pairs(A,site)
        assert close(diagonal(np.diag(H),True),np.diag(np.diag(H)),rtol=0,atol=0)
        bad=H.copy();bad[0,1]+=1e-3
        assert not close(A,bad,rtol=0,atol=1e-4)
    mass=np.array([1.,2.,3.]);charge=np.array([-1.,1.,1.]);birth=rng.normal(size=(3,3));V=2.
    cases=[([4,3,1],[1,1,0],[2,1,1]),([0,0,0],[0,0,0],[3,2,1]),([4,3,1],[4,3,1],[0,0,0])]
    for n,r,a in cases:
        n,r,a=map(lambda v:np.array(v,float),(n,r,a));new=n-r+a
        v=rng.normal(size=(3,3));x=(np.sign(charge)*np.sqrt(V*mass*n))[:,None]*v
        coef,shift=event_affine(n,r,a,birth,V,mass,charge)
        expected=np.divide((n-r)[:,None]*v+a[:,None]*birth,new[:,None],out=np.zeros_like(v),where=new[:,None]>0)
        expected*= (np.sign(charge)*np.sqrt(V*mass*new))[:,None]
        assert np.allclose(coef*x.ravel()+shift,expected.ravel()) and np.max(coef)<=1
        # Exact scalar inequality for every active population fixture.
        for N,R,A in zip(n,r,a):
            N,R,A=map(lambda z:S.Rational(float(z)),(N,R,A))
            assert (N-R)**2<=N*(N-R+A)
    L=csr_matrix([[1.,0.],[0.,1.],[.5,-.5]]);R=csr_matrix([[1.,0.,0.],[0.,1.,0.]])
    hist=coefficient_reopen(rng.normal(size=(4,3,3)),rng.normal(size=(4,3,2)),L,R)
    assert hist['reconstruction_error']<1e-12
    # Actual and shadow see identical contractive affine dynamics, distinct
    # reference trajectory. Midpoint of scalar local Cayley is contractive.
    H=np.diag([-.5,-1.,-.25]);dt=.2;I=np.eye(3)
    C=np.linalg.solve(I-dt*H/2,I+dt*H/2);force=np.array([.1,.2,0.]);shift=np.linalg.solve(I-dt*H/2,dt*force)
    rates=np.array([.5,1.,.25]);x=np.zeros(3);coarse=np.zeros(2);bound=0.;work_error=0.
    for k in range(8):
        old=x.copy();lift=L@coarse;coarse=rng.normal(size=2)*.1
        x=C@old+shift;y=C@lift+shift
        mid=(old+x)/2;shadow_mid=(lift+y)/2;work=dt*float(rates@(mid*mid));wc=float(rng.uniform(0,.02))
        rec=residual_step(x,y,L@coarse,bound,shadow_mid,rates,dt,wc,work)
        bound=rec['error_bound_candidate'];work_error+=rec['work_error_bound_candidate_J']
        assert rec['endpoint_error']<=bound+1e-12
    model=dict(energy_masses=(np.ones(1),np.ones(1)),material_map=np.array([[.3,-.2,.1]]))
    pop=np.array([[5.,3.,2.]]);theta=np.array([20.]);vol=np.ones(1);alpha=np.array([.2,.1]);cap=np.ones(1);cool=np.ones(1);rows=[dict(te=1000.)];neutral=np.zeros((1,11));neutral[:,1:4]=[1e15,2e15,1.5e15]
    h=.05; n=pop[0].copy();max_ratio=0.;last=None
    def collision(T):
        O,N2,O2=neutral[0,1:4]
        return 2.33e-17*N2*(1-1.21e-4*T)*T+1.82e-16*O2*(1+.036*np.sqrt(T))*np.sqrt(T)+8.9e-17*O*(1+5.7e-4*T)*np.sqrt(T)
    def step(N,Th,lim=False):
        # Independent small serial Cayley product of a field and three currents.
        local=np.array([.4,collision(1000.+Th),.7,.8]);T=np.diag((1-h*local/2)/(1+h*local/2));ev=np.eye(4)
        if not lim:
            after=N.copy();after[1:]*=np.exp(-h*alpha*N[0]);after[0]=sum(after[1:]);ev[1:,1:]=np.diag(np.sqrt(after/N))
            for j in range(3):
                A=np.array([[0.,-.3*np.sqrt(after[j]/mass[j])*abs(charge[j])],[.3*np.sqrt(after[j]/mass[j])*abs(charge[j]),0.]])
                Q=np.linalg.solve(np.eye(2)-h*A/2,np.eye(2)+h*A/2);T[[0,j+1],:]=Q@T[[0,j+1],:]
        return T@ev
    T=step(n,0.,True)
    for k in range(65):
        e=tail_envelope(model,pop,theta,vol,rows,neutral,mass,charge,alpha,cap,cool,h,k)
        last=e['operator_step_error_upper_candidate'];actual=step(n,theta[0]*np.exp(-h*(k+.5)))
        ratio=np.linalg.norm(actual-T,2)/last;max_ratio=max(max_ratio,ratio);assert ratio<=1+1e-12
        n[1:]*=np.exp(-h*alpha*n[0]);n[0]=sum(n[1:])
    ref=S.diag(S.Rational(1,2),S.Rational(3,4),1);K=S.eye(3)[:,:2]
    yes=exact_uniform_block(ref,K,1,'1/16');assert yes['conditional_decay_proved'] and yes['block_rho_upper']=='13/16'
    assert not exact_uniform_block(ref,S.eye(3),1,'0')['conditional_decay_proved']
    assert not exact_uniform_block(ref,K,1,'1/2')['conditional_decay_proved']
    print(dict(status='EVOLUTION_TAIL_LOCAL_PASS',storage_cases=3,affine_cases=3,history_reopen=hist['reconstruction_error'],residual_steps=8,final_state_bound=bound,work_error_bound=work_error,tail_steps=65,max_operator_bound_ratio=max_ratio,last_tail_bound=last,exact_block= yes['block_rho_upper'],negative_controls=2))
if __name__=='__main__':run()
