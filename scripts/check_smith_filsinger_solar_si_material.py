"""SI seven-edge material allocation and causal port optimisation.
Ideal source-matched current subspaces, not native circuit or physical source.
Run with pinned SI covariance checker as argv[1].
"""
import hashlib,sys,json
from pathlib import Path
raw=Path(sys.argv[1]).read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='1a3a2df7892833ac4560d462c5d5843222767fff'
exec(compile(raw.decode().split('\nrows=[];maxledger=')[0],sys.argv[1],'exec'))
# Equal conductor volume within each aperture envelope. Assumed material.
rho=1.68e-8; jmax=1e6; persistence=.9
prob=np.full((3,3),(1-persistence)/2);np.fill_diagonal(prob,persistence)
probs=[np.ones(3)/3],prob,[np.ones(3)/3]
# Exact volume-allocation loss identity, Cauchy lower bound.
x,y,a,b=sp.symbols('x y a b',positive=True)
assert sp.cancel((x*x/a+y*y/b)*(a+b)-(x+y)**2-(b*x-a*y)**2/(a*b))==0
# Same exact geodesic edges, recover lengths from degree-one TE columns:
# ||T_TE||=sqrt(3/2)*theta, independent of orientation.
def policy_material(H,V,ps,rank):
    ev,U=np.linalg.eigh(H);assert min(ev)>0
    W=(U/np.sqrt(ev))@U.conj().T; B=W@V
    value=0.; curr=[]
    for p in ps:
        ev,U=np.linalg.eigh((B*p)@B.conj().T);U=U[:,-rank:]
        i=W@U@(U.conj().T@B)/2;curr.append(i)
        value+=sum(ev[-rank:])/(4*len(ps))
    return float(value),curr

def bound_noshell(V,length,volume,ps,rank):
    # For fixed probabilities, weighted covariance written in source coordinates;
    # linear in allocated volume. Sum of top eigenvalues is convex in volume.
    B=V*np.sqrt(volume/(rho*length**2))[:,None];out=0.
    for p in ps:
        X=B*np.sqrt(p);out+=np.linalg.eigvalsh(X.conj().T@X)[-rank:].sum()/(4*len(ps))
    return float(out)
# Equal material loop: N turns of perimeter ell; cross section V/(N ell).
# R=rho (N ell)^2/V; matched Faraday power independent of N.
Nturn,ell,Vcu,om,Bfield,area0,rhos=sp.symbols('N ell Vcu omega B area rho',positive=True)
assert sp.cancel((om*Nturn*area0*Bfield)**2/(4*rhos*(Nturn*ell)**2/Vcu)-om**2*area0**2*Bfield**2*Vcu/(4*rhos*ell**2))==0
aspect0=sp.symbols('aspect',positive=True)
assert sp.factor((sp.sqrt(aspect0)+1/sp.sqrt(aspect0))**2-4)==(aspect0-1)**2/aspect0
rows=[];maxledger=0.;maxpair=0.;maxj=0.;evaluations=0
for f in (.005,.05,3.915,7.83):
    AA,BB,CC,DD,S,Z,V=shell(f);u=np.eye(16)[:,[0,1,3]]/np.sqrt(kappa);voc=V@u
    for area,aspect,angle in product((1.,1e6),(1.,1.5,(1+np.sqrt(5))/2,2.),(0.,np.pi/4,np.pi/2)):
        T=trace(area,aspect,angle);length=R*np.linalg.norm(T[:,:3],axis=1)/np.sqrt(1.5)
        # Square reference has 5 side lengths (four half horizontal, three vertical).
        total=5*np.sqrt(area)*1e-6;uniform=total*length/length.sum()
        Vp=T@voc;Zp=T@Z@T.T/kappa;H=(Zp+Zp.conj().T)/2
        # floor is a fraction of uniform cross section (strictly positive topology).
        for floor in (.1,.5,1.):
            alloc=[uniform]+[floor*uniform+(1-floor)*total*np.eye(7)[k] for k in range(7)]
            best=[None]*3; upper=np.zeros(3)
            for volume in alloc:
                assert abs(volume.sum()/total-1)<1e-12 and min(volume)>0
                cross=volume/length;rc=rho*length**2/volume;Rcu=np.diag(rc)
                for mode,(ps,rank) in enumerate(zip(probs,(1,1,7))):
                    w,cur=policy_material(H+Rcu,Vp,ps,rank);evaluations+=1
                    upper[mode]=max(upper[mode],bound_noshell(Vp,length,volume,ps,rank))
                    den=max(float(np.max(abs(i)/cross[:,None])) for i in cur);maxj=max(maxj,den)
                    # Explicit RMS per-state density cap. All reported ideal solutions satisfy it.
                    assert den<=jmax
                    terminal=heat=natural=loss=0.
                    for i,p in zip(cur,ps):
                        j=T.T@i/kappa;e=voc-Z@j;h=-yg*e-j;e1=AA@e+BB@h;h1=CC@e+DD@h
                        nat=1-kappa*np.sum(abs(e1-u)**2,axis=0)
                        ext=kappa*(np.sum((e1.conj()*(S@e1)).real,axis=0)+yg*np.sum(abs(e)**2,axis=0)+np.sum((e.conj()*h-e1.conj()*h1).real,axis=0))
                        cu=np.sum(rc[:,None]*abs(i)**2,axis=0);port=np.sum((i.conj()*(T@e)).real,axis=0)
                        pair=kappa*np.sum((j.conj()*e).real,axis=0)
                        maxpair=max(maxpair,float(np.max(abs(pair-port))))
                        maxledger=max(maxledger,float(np.max(abs(nat-ext-port))))
                        terminal+=p@(port-cu)/len(ps);heat+=p@cu/len(ps);natural+=p@nat/len(ps);loss+=p@ext/len(ps)
                    assert abs(terminal-w)<1e-12*max(abs(w),1e-30)
                    cand=dict(power=w,heat=float(heat),natural=float(natural),external_loss=float(loss),volume=volume.tolist(),density=den)
                    if best[mode] is None or w>best[mode]['power']:best[mode]=cand
            lower=np.array([b['power'] for b in best]);assert np.all(lower<=upper+1e-13*np.maximum(upper,1e-30))
            rows.append(dict(f=f,area=area,aspect=aspect,angle=float(angle),floor=floor,total_volume=total,lower=lower.tolist(),upper=upper.tolist(),best=best))
assert maxledger<1e-12 and maxpair<1e-12
# Relative gain enclosure across all continuous material allocations, on sampled geometry grid.
summary=[]
for area,floor in product((1.,1e6),(.1,.5,1.)):
    rr=[r for r in rows if r['area']==area and r['floor']==floor];lo=np.max([r['lower'] for r in rr],axis=0);hi=np.max([r['upper'] for r in rr],axis=0)
    active=max(rr,key=lambda r:r['lower'][1]);fixed=max(rr,key=lambda r:r['lower'][0]);full=max(rr,key=lambda r:r['lower'][2])
    summary.append(dict(area=area,floor=floor,lower=lo.tolist(),upper=hi.tolist(),gain_interval=[float(lo[1]-hi[0]),float(hi[1]-lo[0])],active_geometry=[active[k] for k in ('f','aspect','angle')],fixed_geometry=[fixed[k] for k in ('f','aspect','angle')],full_geometry=[full[k] for k in ('f','aspect','angle')],max_active_density=active['best'][1]['density'],controller_1uW_incident_W_sufficient=float(1e-6/(lo[1]-hi[0])),controller_1uW_incident_W_necessary=float(1e-6/(hi[1]-lo[0])),switch_budget_lower_J=float((lo[1]-hi[0])/(1-persistence)),switch_budget_upper_J=float((hi[1]-lo[0])/(1-persistence))))
print(json.dumps(dict(status='CONDITIONAL_SI_MATERIAL_COVARIANCE',rows=rows,summary=summary,evaluations=evaluations,max_ledger_W=maxledger,max_pair_W=maxpair,max_density_A_m2=maxj,physical_admission=False),indent=2))
