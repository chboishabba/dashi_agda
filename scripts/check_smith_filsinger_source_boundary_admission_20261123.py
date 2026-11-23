#!/usr/bin/env python3
"""Filsinger/HAARP/SURA/Duga calibrated-source admission, exact rational controls.

Independent reuse-oriented CONSUMER of #1537 J21/J22, #1540 ionosphere/Duga,
and #1524 Maxwell ADE source owners; does not reproduce their solvers.
All metered examples here are SYNTHETIC, not actual SI measurements.
No original source-to-port, gravity, health, or energy-harvesting claims.
"""
import json
from fractions import Fraction as Q
import sympy as S

CHANNELS=('duga_hf','haarp_electrojet','haarp_f_region','sura_lh_whistler')
FIELDS=('incident','reflected','load','controller','heat','storage',
        'receiver_VI','antenna_polarization','clock','conversion',
        'source_identity','calibration')

def iv(a,b): 
    a,b=Q(str(a)),Q(str(b))
    assert 0<=a<=b
    return (a,b)

def energy_range(d):
    x=[d[k] for k in ('incident','controller','reflected','load','heat','storage')]
    return (x[0][0]+x[1][0]-sum(y[1] for y in x[2:]),
            x[0][1]+x[1][1]-sum(y[0] for y in x[2:]))

def admit(d):
    missing=[k for k in FIELDS if d.get(k) is None]
    if missing:return {'admitted':False,'reason':'MISSING_PHYSICAL_BOUNDARY','missing':missing}
    if d.get('units')!='SI':return {'admitted':False,'reason':'UNMEASURED_SI_CALIBRATION'}
    if not d.get('same_apparatus_cycle'):return {'admitted':False,'reason':'NO_SHARED_CYCLE'}
    if d['incident'][0]<=0:return {'admitted':False,'reason':'ZERO_INCIDENT_DENOMINATOR'}
    z=energy_range(d)
    if not z[0]<=0<=z[1]:return {'admitted':False,'reason':'SIGNED_LEDGER_INCOMPATIBLE'}
    return {'admitted':True,'receiver_efficiency_interval':
            [str(d['load'][0]/d['incident'][1]),str(d['load'][1]/d['incident'][0])],
            'energy_residual_interval':[str(v) for v in z],
            'source_only':d['controller']==(Q(0),Q(0))}

def test():
    g=S.symbols('g0:4',real=True)
    f=S.symbols('f0:4',real=True,nonzero=True)
    y=sum(a*b for a,b in zip(g,f))
    assert S.Matrix([y]).jacobian(g).rank()==1
    assert S.diag(*f).rank()==4
    lam=S.symbols('lambda',positive=True)
    assert S.simplify((g[0]*lam)*(f[0]/lam)-g[0]*f[0])==0
    a,b,p=S.symbols('a b phi',real=True)
    h=a+b*S.exp(S.I*p)
    assert S.trigsimp(S.expand_complex(h*S.conjugate(h))-a*a-b*b-2*a*b*S.cos(p))==0

    # Historical HF radar windows versus pulse on-time (illustrative 4ms).
    T=S.Rational(100,1000)
    assert 4*S.Rational(7,1000)/T==S.Rational(7,25)
    assert 4*S.Rational(4,1000)/T==S.Rational(4,25)
    assert 1-4*S.Rational(4,1000)/T==S.Rational(21,25)
    assert S.Integer(10)!=S.Rational(783,100)

    # J21 original-source finite coil resistance, restored storage, driver OFF.
    Rc=S.Rational(1,20);G=S.Rational(13,25)
    cap=1/(1+Rc*G)
    incident=S.Rational('90.4778684234')
    outgoing=S.Rational('31.0579370287')
    load=S.Rational('46.5616600780')
    assert cap==S.Rational(500,513)
    assert 0<load/incident<1-outgoing/incident<cap<1

    # A full metered SI record is only a deliberately SYNTHETIC benchmark.
    sample=dict(incident=iv(100,101),reflected=iv(19,21),load=iv(49,51),
                controller=iv(0,0),heat=iv(29,31),storage=(Q(-1),Q(1)),
                receiver_VI='synthetic trace',antenna_polarization='synthetic',
                clock='synthetic',conversion='synthetic',source_identity='synthetic',
                calibration='synthetic',units='SI',same_apparatus_cycle=True)
    good=admit(sample)
    assert good['admitted'] and good['source_only']
    assert good['receiver_efficiency_interval']==['49/101','51/100']
    for key in FIELDS:
        d=sample.copy();d.pop(key)
        assert not admit(d)['admitted'],key
    d=sample|{'load':iv(150,151)}
    assert admit(d)['reason']=='SIGNED_LEDGER_INCOMPATIBLE'
    d=sample|{'same_apparatus_cycle':False}
    assert admit(d)['reason']=='NO_SHARED_CYCLE'
    d=sample|{'units':'J18 dimensionless'}
    assert admit(d)['reason']=='UNMEASURED_SI_CALIBRATION'
    d=sample|{'incident':iv(0,0)}
    assert admit(d)['reason']=='ZERO_INCIDENT_DENOMINATOR'
    assert not admit({k:None for k in FIELDS})['admitted']
    return {'status':'PASS','scope':'EXACT_SYNTHETIC_BOUNDARY_ONLY',
            'sympy_version':S.__version__,'sources':CHANNELS,
            'single_receiver_rank':1,'independently_metered_rank':4,
            'coherent_cross_term':'2*a*b*cos(phi)',
            'strict_J21_finite_coil_efficiency_ceiling':str(cap),
            'duga_illustrative_on_fraction':'4/25',
            'duga_illustrative_off_fraction':'21/25',
            'synthetic_example':good,
            'missing_field_negative_controls':len(FIELDS),
            'other_fail_closed_controls':4,
            'physical_Filsinger_source_admitted':False,
            'gravity_source_admitted':False,'github_ci':False}

if __name__=='__main__':print(json.dumps(test(),indent=2))
