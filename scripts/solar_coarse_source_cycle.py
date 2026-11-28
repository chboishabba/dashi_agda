"""Coarse fixed incident-port periodic ADE comparison, exact synthetic triangle.
No measured source, no physical switching cost model or stability admission.
"""
import sympy as S
from itertools import combinations
from solar_gauss_ade_weld import incidence,augmented_step
from solar_coherent_reverse_weld import periodic
from solar_coarse_endpoint import verdict
from fractions import Fraction


def fixture():
    d=incidence([list(combinations(range(3),k)) for k in (1,2,3,4)])
    return d,dict(h=S.Rational(1,5),alpha=S.Integer(2),omega2=S.Integer(3),gamma=S.Rational(1,2),sigma=S.Rational(1,4),load=S.Rational(1,3),p=S.Integer(1))


def cycle(d,c,eps,incident):
    h,alpha,omega2,gamma,sigma,load,p=(c[k] for k in ('h','alpha','omega2','gamma','sigma','load','p'))
    eps=list(map(S.Rational,eps));incident=list(map(S.Matrix,incident));ne,nf=d[1].cols,d[1].rows
    if len(eps)!=len(incident)+1 or eps[0]!=eps[-1] or min(eps)<=0 or min(h,alpha,omega2,p)<=0 or min(gamma,sigma,load)<0:raise ValueError('cycle chart')
    z=S.zeros(3*ne+nf,1);off=S.zeros(ne,1);mb=[S.Integer(1)]*nf
    def step(k,x,j):return augmented_step(d,[eps[k]]*ne,[eps[k+1]]*ne,mb,alpha,omega2,gamma,sigma+p*p,load,x,j,off,h)
    maps=[];js=[2*p*a for a in incident]
    for k,j in enumerate(js):
        r=step(k,z,j);maps.append((r['T'],r['F']))
    states,M,ker=periodic(maps,js)
    W={k:S.Integer(0) for k in ('incident','reflected','natural','ohmic','relaxation','useful','modulation','gross_pump')}
    for k,(a,j) in enumerate(zip(incident,js)):
        r=step(k,states[k],j);assert r['state']==states[k+1]
        e=(states[k][:ne,:]+states[k+1][:ne,:])/2
        X=h*(e.T*e)[0];inc=h*(a.T*a)[0];refl=h*((a-p*e).T*(a-p*e))[0]
        assert r['natural']-p*p*X==inc-refl
        W['incident']+=inc;W['reflected']+=refl;W['natural']+=inc-refl
        W['ohmic']+=sigma*X;W['relaxation']+=r['loss']-(sigma+p*p)*X
        W['useful']+=r['useful'];W['modulation']+=r['modulation'];W['gross_pump']+=max(0,r['modulation'])
    assert W['natural']+W['modulation']==W['useful']+W['ohmic']+W['relaxation']
    W['ideal_signed_net']=W['useful']-W['modulation'];W['no_recovery_net']=W['useful']-W['gross_pump']
    W['universal_net_upper']=W['incident']*p*p/(p*p+sigma)
    assert W['no_recovery_net']<=W['ideal_signed_net']<=W['universal_net_upper']
    return dict(work=W,periodic=True,initial=states[0],monodromy=M,conserved_dimension=len(ker),physical_admission=False)


def static_optimum(d,c,lo,hi,incident_work):
    """Exact fixed-load best stationary scalar eps in [lo,hi], quarter-clock tone.
    Source is one transverse mode w=d1.T, mb=1; no claim about other geometries.
    """
    h,alpha,omega2,gamma,sigma,load,p=(c[k] for k in ('h','alpha','omega2','gamma','sigma','load','p'))
    lo,hi=map(S.Rational,(lo,hi));assert 0<lo<=hi and d[1].rows==1
    delta=2*S.I/h;k=(d[1]*d[1].T)[0]
    Z0=sigma+load+p*p+k/delta+alpha*delta/(delta**2+gamma*delta+omega2)
    unconstrained=S.simplify(-S.im(Z0)/S.im(delta));eps=max(lo,min(hi,unconstrained))
    Z=Z0+eps*delta;eta=S.simplify(4*p*p*load/(Z*S.conjugate(Z)))
    assert 0<=eta<=1
    return dict(eps=eps,unconstrained_eps=unconstrained,useful=S.simplify(incident_work*eta),efficiency=eta)


def run():
    d,c=fixture();w=d[1].T;off=S.zeros(w.rows,1);src=[w,off,-w,off]
    active=cycle(d,c,[1,2,1,2,1],src);W=active['work']
    opt=static_optimum(d,c,1,2,W['incident']);passive=cycle(d,c,[opt['eps']]*5,src)
    assert passive['work']['useful']==opt['useful']
    offa=cycle(d,c,[1,2,1,2,1],[off]*4);offp=cycle(d,c,[opt['eps']]*5,[off]*4)
    assert offa['work']['no_recovery_net']==offp['work']['no_recovery_net']==0
    # Exact candidate contrast, not an all-switching impossibility.
    contrast=W['no_recovery_net']-opt['useful'];assert contrast<0
    upper=W['universal_net_upper']-opt['useful'];assert upper>0
    # A desired gain above this source-domain ceiling is impossible; smaller is unresolved.
    for gain,expected in [(upper+S.Rational(1,100),'EMPTY_ON_DECLARED_DOMAIN'),(upper/2,'UNRESOLVED')]:
        bounds=(Fraction(contrast-gain),Fraction(upper-gain))
        assert verdict(bounds,domain_upper=True)==expected
    print(dict(status='COARSE_SOURCE_CYCLE_PASS',passive_eps=str(opt['eps']),passive_useful=float(opt['useful']),active_net=float(W['no_recovery_net']),active_signed_net=float(W['ideal_signed_net']),incident=float(W['incident']),universal_net_upper=float(W['universal_net_upper']),contrast=float(contrast),unresolved_headroom=float(upper),physical_admission=False))
if __name__=='__main__':run()
