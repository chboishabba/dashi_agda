"""Phase-resolved rank-limited access: exact C3 control and planar donor replay.
Ideal modal selection, paid-cost budgets only; no physical HF actuator or calibration.
"""
import ast, hashlib, json
from pathlib import Path
import numpy as np
import sympy as s
# Exact reciprocal lossless mixer: forward U, reverse U^T (not U dagger).
w=(-1+s.I*s.sqrt(3))/2
U=s.Matrix(3,3,lambda j,k:w**((-j*k)%3)/s.sqrt(3))
clean=lambda A:A.applyfunc(s.simplify)
assert clean(U.H*U)==s.eye(3)
S=s.zeros(6);S[:3,3:]=U.T;S[3:,:3]=U
assert S.T==S and clean(S.H*S)==s.eye(6)
for r in range(3):
    a=s.Matrix([w**((r*k)%3)/s.sqrt(3) for k in range(3)])
    assert clean(U*a)==s.eye(3)[:,r]
    for j in range(3):
        P=s.eye(3)[:,j]*s.eye(3)[j,:];b=U.T*(s.eye(3)-P)*U*a
        assert s.simplify((b.H*b)[0])==int(j!=r)
# Fixed one-channel projector sees trace(covariance)/3; adaptive prior-state
# predictor with Markov persistence p >= 1/3 sees p. No oracle assumption.
p,c=s.symbols('p c',real=True)
assert s.expand(p-c*(1-p)-s.Rational(1,3)-(p-s.Rational(1,3)-c*(1-p)))==0
# Replay actual donor operator definition, not its grid or a retyped model.
path=Path(__file__).with_name('check_smith_filsinger_solar_ground_p1.py')
raw=path.read_bytes();blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
assert blob=='1a9ad6f6ba05ac1cc6648831160937fd0cd91a6b'
mu=4*np.pi*1e-7;eps=8.8541878128e-12
node=next(n for n in ast.parse(raw).body if isinstance(n,ast.FunctionDef) and n.name=='operator')
exec(compile(ast.Module(body=[node],type_ignores=[]),str(path),'exec'))
# RMS modes, rank-one current subspace, ideal complex match. Each fixed
# rank-one subspace is optimized over ALL complex directions, not angles.
pol=np.array([[1,0],[0,1],[1,1j],[1,-1j]],complex);pol[2:]/=np.sqrt(2)
rows=[];maxerr=0.;maxair=0.;nworld=0
for f in (.005,.05):
 for lam in (1000,10000):
  for sp in (3,5,20):
   for sh in (0,5):
    for sig in (.001,.01,.1):
     ya,C,D,F,Yg,sheet,M,Z=operator(f,lam,sp,sh,sig)
     H=(Z+Z.conj().T)/2;ev,W=np.linalg.eigh(H);R=(W/np.sqrt(ev))@W.conj().T
     V=np.array([np.linalg.solve(M,2*ya*a) for a in pol]);A=(R@V.T).T
     def best(prob):
        cov=(A.T*prob)@A.conj();e,u=np.linalg.eigh(cov);return u[:,-1],float(e[-1]/4)
     def work(u,i):
        global maxerr,maxair,nworld
        # j in span(Ru); exact conjugate match for that scalar port.
        ei=pol[i];v=V[i];j=R@u*np.vdot(u,A[i])/2;eg=v-Z@j;hg=Yg@eg+j
        es=C@eg+D@hg;hs=F@eg+C@hg;inc=ya*np.vdot(ei,ei).real
        ref=ya*np.vdot(es-ei,es-ei).real;ion=np.vdot(es,sheet@es).real;soil=np.vdot(eg,Yg@eg).real;load=np.vdot(j,eg).real
        err=inc-ref-ion-soil-load;air=np.vdot(es,hs).real-np.vdot(eg,hg).real
        maxerr=max(maxerr,abs(err));maxair=max(maxair,abs(air));nworld+=1
        assert min(ref,ion,soil,load)>-1e-10 and abs(err)<1e-9 and abs(air)<1e-9
        assert abs(load-abs(np.vdot(u,A[i]))**2/4)<1e-10
        return load,inc-ref
     uf,pfixed=best(np.ones(4)/4);fixed=np.array([work(uf,i) for i in range(4)]).mean(axis=0)
     assert abs(fixed[0]-pfixed)<1e-10
     full=np.sum(abs(A)**2)/16
     for persist in (.25,.5,.9,.99):
        T=np.full((4,4),(1-persist)/3);np.fill_diagonal(T,persist)
        dirs=[best(t)[0] for t in T];pred=sum(best(t)[1] for t in T)/4
        actual=sum(T[j,i]*np.array(work(dirs[j],i))/4 for j in range(4) for i in range(4))
        assert abs(actual[0]-pred)<1e-10 and pfixed-1e-10<=pred<=full+1e-10
        # Stationary Markov changes of previous observed state. Charge only
        # changes in the actual projective direction, not arbitrary phase.
        rate=sum(T[j,i]/4 for j in range(4) for i in range(4) if abs(np.vdot(dirs[j],dirs[i]))<1-1e-10)
        budget=(pred-pfixed)/ya
        rows.append(dict(f=f,lambda_km=lam,Pedersen=sp,Hall=sh,soil=sig,persist=persist,fixed=pfixed/ya,adaptive=pred/ya,full=full/ya,delta_access=(actual[1]-fixed[1])/ya,budget=budget,switch_probability=rate,cost_per_switch_budget=budget/rate if rate else None))
print(json.dumps(dict(status='CONDITIONAL_CAUSAL_PHASE_ACCESS',donor_blob=blob,exact_C3=dict(fixed='1/3',causal='p for p>=1/3',oracle='1',cost_threshold='(p-1/3)/(1-p) per incident block energy for p<1'),rows=len(rows),loaded_worlds=nworld,max_energy_residual=maxerr,max_air_residual=maxair,best=max(rows,key=lambda r:r['budget']),largest_cost_budget=max((r for r in rows if r['cost_per_switch_budget'] is not None),key=lambda r:r['cost_per_switch_budget']),positive_budget=sum(r['budget']>1e-12 for r in rows),positive_access_and_budget=sum(r['budget']>1e-12 and r['delta_access']>1e-12 for r in rows),by_p=[dict(p=p,best=max((r for r in rows if r['persist']==p),key=lambda r:r['budget'])) for p in (.25,.5,.9,.99)],scope='Synthetic Markov polarization blocks, steady narrowband RMS model; independent block transitions and settling omitted. Fixed rank-one arbitrary complex current subspace, adaptive rank-one delayed predictor, unrestricted rank-two comparator. Resource dimension only, not equal physical hardware. Cost budget before sensing/switching/standby/transients; no HF actuator, regional data or solar watts.'),indent=2,default=lambda v:v.item()))
