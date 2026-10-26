"""Physical unforced Galerkin NO-GO for the universal R734/R735 W2 leaf.

DASHI-original exact witness, with historical attribution to the
Navier--Stokes/Leray equation, Waleffe 1992 helical triad calculus,
and the existing DASHI R691/R700/R730/R734 source definitions.

Six real Fourier modes with positive curl-helicity initially have
zero H+ cross H- mixed carrier but strictly POSITIVE dyadic-weighted
critical production. Amplitude scaling violates the original positive-
margin W2 inequality on a short interval. NOT Navier-Stokes blowup.
"""
from collections import defaultdict
from functools import lru_cache
import sympy as S

I=S.I
P=(1,0,0); Q=(0,1,2); K=(1,1,2)
SEEDS={P:(0,1,1),Q:(1,0,0),K:(1,-1,0)}
def n2(k):return sum(a*a for a in k)
def minus(k):return tuple(-a for a in k)
def weight(k):return 1<<(max(map(abs,k))-1).bit_length()
def h(k,v,sign):
    return (v+sign*I*S.Matrix(k).cross(v)/S.sqrt(n2(k)))/2
def physical_u():
    u={k:h(k,S.Matrix(v),1) for k,v in SEEDS.items()}
    u.update({minus(k):S.conjugate(v) for k,v in list(u.items())})
    return u
def projected_NS_nonlinearity(u,cut=2):
    raw=defaultdict(lambda:S.zeros(3,1))
    for p,v in u.items():
        for q,w in u.items():
            k=tuple(p[i]+q[i] for i in range(3))
            raw[k]+=S.Matrix(q).dot(v)*w
    out={}
    for k,v in raw.items():
        if n2(k)==0 or max(map(abs,k))>cut:continue
        kv=S.Matrix(k)
        out[k]=-I*(v-kv*kv.dot(v)/n2(k))
    return out
@lru_cache(maxsize=1)
def critical_data():
    u=physical_u();nl=projected_NS_nonlinearity(u)
    X=sum((weight(k)*(S.conjugate(v).T*v)[0] for k,v in u.items()),S.Integer(0))
    D=sum((weight(k)*n2(k)*(S.conjugate(v).T*v)[0] for k,v in u.items()),S.Integer(0))
    Pcrit=sum((2*weight(k)*S.re((S.conjugate(v).T*nl.get(k,S.zeros(3,1)))[0])
               for k,v in u.items()),S.Integer(0))
    return S.simplify(X),S.simplify(D),S.simplify(S.expand_complex(Pcrit))
def test_real_transverse_pure_plus_helicity_six_mode_state():
    u=physical_u()
    assert len(u)==6
    for k,v in u.items():
        assert S.simplify(S.Matrix(k).dot(v))==0
        assert S.simplify(v-S.conjugate(u[minus(k)]))==S.zeros(3,1)
        assert S.simplify(h(k,v,+1)-v)==S.zeros(3,1)
        assert S.simplify(h(k,v,-1))==S.zeros(3,1)
def test_same_cutoff_projected_NS_force_reality_and_transverse():
    nl=projected_NS_nonlinearity(physical_u(),2)
    assert nl
    for k,v in nl.items():
        assert S.simplify(S.Matrix(k).dot(v))==0
        assert S.simplify(v-S.conjugate(nl[minus(k)]))==S.zeros(3,1)
def test_exact_literal_dyadic_critical_production_positive():
    X,D,Pcrit=critical_data()
    assert X==8 and D==36
    assert Pcrit==(5+S.sqrt(5)-S.sqrt(30))/10
    assert S.simplify(Pcrit>0)==S.true
def test_original_selected_mixed_helical_work_zero_at_initial_time():
    u=physical_u()
    # All H- coefficients vanish, including the conjugate -modes.
    for p,a in u.items():
        for q,b in u.items():
            assert S.simplify(h(p,a,+1).cross(h(q,b,-1)))==S.zeros(3,1)
def test_amplitude_scaling_defeats_every_positive_r734_margin():
    _,D,Pcrit=critical_data()
    amp=S.Integer(512);nu=S.Integer(1)
    derivative=S.factor(amp**3*Pcrit-2*nu*amp**2*D)
    assert S.simplify(amp*Pcrit-2*nu*D>0)==S.true
    assert S.simplify(derivative>0)==S.true
    for margin in [S.Rational(1,1000),S.Rational(1,10),1,2,10]:
        assert S.simplify(derivative+margin*amp**2*D>0)==S.true
def test_short_time_W2_failure_uses_actual_initial_derivatives():
    _,D,Pcrit=critical_data()
    for a in [1,2,7,512]:
        assert S.simplify(a**3*Pcrit-2*a*a*D-
                          a*a*(a*Pcrit-2*D))==0
    # Galerkin NS is a smooth finite-dimensional ODE:
    # E_M(0)=E_M'(0)=0, signed weighted W rate(0)=0.
    # At a=512, X'(0)>0. Thus [X-12 E_M]' + delta D
    # exceeds 12 W'(0) for EVERY delta>0. By continuity there
    # exists T>0 on which the integrated R734 W2 is false.
    assert S.simplify(512*Pcrit-72>0)==S.true

def test_unweighted_nonlinear_kinetic_energy_conserved():
    u=physical_u();nl=projected_NS_nonlinearity(u)
    energy_work=sum((2*S.re((S.conjugate(v).T*nl.get(k,S.zeros(3,1)))[0])
                     for k,v in u.items()),S.Integer(0))
    assert S.simplify(S.expand_complex(energy_work))==0
def test_real_full_NS_forcing_generates_negative_helicity():
    # Pure-plus INITIAL DATA do not turn the full NSE into the
    # separately regular helical-DECIMATED model of Biferale--Titi.
    u=physical_u();nl=projected_NS_nonlinearity(u)
    hm=h(Q,nl[Q],-1)
    hmnorm=S.simplify(S.expand_complex((S.conjugate(hm).T*hm)[0]))
    assert S.simplify(hmnorm>0)==S.true

def test_rational_interval_certificate_for_margin_failure():
    _,D,Pcrit=critical_data()
    # sqrt(5)>2 and sqrt(30)<11/2, both by integer squaring.
    assert 5>4 and S.Rational(121,4)>30
    assert S.simplify(Pcrit>S.Rational(3,20))==S.true
    # Strict RATIONAL lower bound on the δ=0 derivative.
    lower=512*S.Rational(3,20)-2*D
    assert lower==S.Rational(24,5)>0

def test_original_R92_R102_helicity_conservation_vs_literal_dyadic_defect():
    # Waleffe |m| signed curl eigenvalue is NOT the R734 dyadic
    # weight 2^ceil(log2 ||m||infty). Reuse existing R92/R102 owners.
    u=physical_u();nl=projected_NS_nonlinearity(u)
    true_helicity_nonlinear=S.simplify(S.expand_complex(sum((
        2*S.sqrt(n2(m))*S.re((S.conjugate(v).T*nl.get(m,S.zeros(3,1)))[0])
        for m,v in u.items()),S.Integer(0))))
    assert true_helicity_nonlinear==0
    exact_defect=S.simplify(S.expand_complex(sum((
        2*(weight(m)-S.sqrt(n2(m)))*
        S.re((S.conjugate(v).T*nl.get(m,S.zeros(3,1)))[0])
        for m,v in u.items()),S.Integer(0))))
    assert S.simplify(exact_defect-critical_data()[2])==0
    true_helicity_mass=S.simplify(sum((
        S.sqrt(n2(m))*(S.conjugate(v).T*v)[0]
        for m,v in u.items()),S.Integer(0)))
    assert true_helicity_mass==2+S.sqrt(5)+2*S.sqrt(6)

def test_general_helicity_negative_sector_and_dyadic_defect_split():
    # Existing R92/R102 signed helicity and R734 dyadic weights:
    # Xw=Hsigned+2*negative_helicity_mass+R_weight.
    w,r,eplus,eminus=S.symbols('w r eplus eminus',real=True)
    assert S.expand(w*(eplus+eminus)-r*(eplus-eminus)
                    -2*r*eminus-(w-r)*(eplus+eminus))==0
    pp,mm=S.symbols('pp mm',real=True)
    assert S.expand(w*(pp+mm)-r*(pp-mm)
                    -2*r*mm-(w-r)*(pp+mm))==0

def test_actual_physical_source_defect_is_all_pure_plus_initial_growth():
    u=physical_u();force=projected_NS_nonlinearity(u)
    signed=negative_tangent=defect_tangent=S.Integer(0)
    for mode,vel in u.items():
        f=force.get(mode,S.zeros(3,1))
        plus=h(mode,vel,+1);minusv=h(mode,vel,-1)
        dp=2*S.re((S.conjugate(plus).T*h(mode,f,+1))[0])
        dm=2*S.re((S.conjugate(minusv).T*h(mode,f,-1))[0])
        radial=S.sqrt(n2(mode));w=weight(mode)
        signed+=radial*(dp-dm)
        negative_tangent+=radial*dm
        defect_tangent+=(w-radial)*(dp+dm)
    assert S.simplify(S.expand_complex(signed))==0
    assert S.simplify(S.expand_complex(negative_tangent))==0
    assert S.simplify(S.expand_complex(defect_tangent-critical_data()[2]))==0
