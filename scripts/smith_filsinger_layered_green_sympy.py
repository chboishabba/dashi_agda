"""Exact reduced three-layer transverse Maxwell Green and restored-cycle audit.

NOT a full 3D dyadic Maxwell solution, SI material identification, measured
solar source, or Agda-kernel proof. All layer values below are rational FIXTURES.
C e'' + (P+H)e' + K e = J_natural + J_control.
G(s) = (s² C + s(P+H) + K)^(-1); antisymmetric Hall H does no work.
"""
from dataclasses import dataclass
import sympy as S

@dataclass(frozen=True)
class Layer:
    inertia: S.Rational
    pedersen: S.Rational
    hall: S.Rational
    shunt: S.Rational

def exact_layers():
    return (Layer(S.Rational(3,2),S.Rational(2,3),S.Rational(1,5),S.Rational(1,2)),
            Layer(S.Rational(1),S.Rational(1,4),S.Rational(0),S.Rational(1,3)),
            Layer(S.Rational(5,4),S.Rational(3,5),S.Rational(-2,7),S.Rational(2,5)))

def matrices(layers=None, couplings=None):
    layers=exact_layers() if layers is None else layers
    couplings=(S.Rational(2,5),S.Rational(3,7)) if couplings is None else couplings
    if len(layers)!=3 or len(couplings)!=2:raise ValueError("expected 3 layers")
    C,P,H,K=(S.zeros(6) for _ in range(4))
    for i,l in enumerate(layers):
        for j in range(2):
            k=2*i+j
            C[k,k]=l.inertia
            P[k,k]=l.pedersen
            K[k,k]=l.shunt
        H[2*i,2*i+1]=l.hall
        H[2*i+1,2*i]=-l.hall
    for i,w in enumerate(couplings):
        for j in range(2):
            a=2*i+j;b=2*(i+1)+j
            K[a,a]+=w;K[b,b]+=w
            K[a,b]-=w;K[b,a]-=w
    return C,P,H,K

def admittance(s,C,P,H,K):
    return s*s*C+s*(P+H)+K

def green_laplace(s,C,P,H,K):
    return admittance(s,C,P,H,K).inv()

def terminal_transfer(G,sensor_layer=0,source_layer=2,pol=0):
    return S.cancel(G[2*sensor_layer+pol,2*source_layer+pol])

def midpoint_step(e,v,natural,control,C,P,H,K,dt=S.Rational(1,4)):
    # Implicit midpoint is CAUSAL in discrete source steps; no future data.
    midv=(2*C/dt+P+H+dt*K/2).inv()*(natural+control+2*C*v/dt-K*e)
    e1=e+dt*midv
    v1=2*midv-v
    U=lambda E,V:S.expand((V.T*C*V+E.T*K*E)[0]/2)
    n=S.expand(dt*(midv.T*natural)[0])
    c=S.expand(dt*(midv.T*control)[0])
    q=S.expand(dt*(midv.T*P*midv)[0])
    hall=S.expand(dt*(midv.T*H*midv)[0])
    return dict(e=e1,v=v1,natural_work=n,controller_work=c,heat=q,
                hall_work=hall,energy_change=S.expand(U(e1,v1)-U(e,v)),
                residual=S.simplify(U(e1,v1)-U(e,v)-n-c+q))

def restored_cycle_audit(*,natural=None,controller=None,load=None,loss=None,
                         initial_storage=None,final_storage=None,
                         independent_natural_meter=False,independent_load_meter=False,
                         original_terminal_calibration=False,
                         double_counted_boundary=False):
    vals=(natural,controller,load,loss,initial_storage,final_storage)
    if any(v is None for v in vals):
        return dict(status="OPEN",reason="missing independent work observation")
    if not all((independent_natural_meter,independent_load_meter,
                original_terminal_calibration)):
        return dict(status="OPEN",reason="original independently metered source/terminal not established")
    if double_counted_boundary:
        return dict(status="REJECT",reason="external Poynting work double-counted")
    n,c,l,q,ui,uf=map(S.Rational,vals)
    if ui!=uf:return dict(status="REJECT",reason="storage not restored")
    if n+c+ui!=l+q+uf:return dict(status="REJECT",reason="energy balance")
    if n<=0 or min(c,l,q)<0:return dict(status="REJECT",reason="source/gain sign")
    return dict(status="CONDITIONAL_LEDGER_PASS",
                natural_required=l+q-c,
                useful_exceeds_controller=bool(l>c),
                hundredfold_load_over_controller=bool(c>0 and l>=100*c))

def uncertainty_gain_certificate(*,natural_interval=None,controller_interval=None,
                                 load_interval=None,loss_interval=None,
                                 storage_change_interval=None,
                                 independent_source=False,
                                 same_original_terminals=False):
    values=(natural_interval,controller_interval,load_interval,
            loss_interval,storage_change_interval)
    if any(v is None or len(v)!=2 for v in values):
        return dict(status="OPEN",reason="missing intervals")
    if not (independent_source and same_original_terminals):
        return dict(status="OPEN",reason="independent original source/terminal unavailable")
    (nl,nu),(cl,cu),(ll,lu),(ql,qu),(dl,du)=[
        tuple(map(S.Rational,v)) for v in values]
    if any(a>b for a,b in ((nl,nu),(cl,cu),(ll,lu),(ql,qu),(dl,du))):
        return dict(status="REJECT",reason="invalid intervals")
    # Source + controller = load + losses + delta all stored states.
    if nu+cu<ll+ql+dl or nl+cl>lu+qu+du:
        return dict(status="REJECT",reason="interval conservation impossible")
    if (dl,du)!=(0,0):
        return dict(status="OPEN",reason="all storage restoration not certified")
    if nl<=0 or cl<=0:
        return dict(status="OPEN",reason="strictly positive sourced work missing")
    return dict(status="CONDITIONAL_INTERVAL_CERTIFICATE",
                robust_load_over_controller_lower=ll/cu,
                hundredfold_robust=bool(ll>=100*cu),
                net_positive_robust=bool(ll>cu))
