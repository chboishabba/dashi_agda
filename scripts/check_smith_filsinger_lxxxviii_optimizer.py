#!/usr/bin/env python3
"""LXXXVIII: exact four-step Maxwell/ADE matched-port recovery controls.
Candidate tuning only; no physical calibration, restored cycle, or CI.
"""
import json
import sympy as S
from smith_filsinger_lorentz_ade_sympy import generator,exact_midpoint,synthetic_cycle_work_receipt
Q=S.Rational
P=((0,0),(1,0),(0,1),(0,0))

def evaluate(Z,G,amp=Q(1)):
    A,B,M=generator(n=2,load_conductance=G+1/Z)
    z=S.zeros(8,1); steps=[]; sums={k:S.Integer(0) for k in
      ('incident','reflected','terminal','other','ohmic','relaxation','storage')}
    for a0,a1 in P:
        a=S.Matrix([a0*amp,a1*amp]);n=S.Matrix([2*a[0]/Z,0]);c=S.Matrix([0,2*a[1]/Z])
        s=exact_midpoint(z,n,c,Q(1,10),A,B,M,load_conductance=G+1/Z)
        assert s['residual']==0
        e=s['mid'][:2,:];b=e-a
        values=dict(incident=Q(1,10)*a.dot(a)/Z,
           reflected=Q(1,10)*b.dot(b)/Z,
           terminal=Q(1,10)*G*e[1]**2,
           other=Q(1,10)*G*e[0]**2,
           ohmic=s['ohmic'],relaxation=s['relaxation'],storage=s['energy_change'])
        assert S.factor(values['incident']-values['reflected']-sum(
          values[k] for k in ('terminal','other','ohmic','relaxation','storage')))==0
        for k,v in values.items():sums[k]+=v
        z=s['z'];steps.append(s)
    r=synthetic_cycle_work_receipt(S.zeros(8,1),steps,M)
    assert r['conservation_residual']==0 and not r['restored_all_4n_states']
    net=S.factor(sums['incident']-sums['reflected'])
    assert net>0 and sums['storage']>=0
    return dict(Z=str(Z),G=str(G),amplitude=str(amp),
      total={k:float(v) for k,v in sums.items()},net=float(net),
      terminal_over_net=float(sums['terminal']/net),
      terminal_over_incident=float(sums['terminal']/sums['incident']),
      capture=float(net/sums['incident']),exact_energy_zero=True,restored=False)

def main():
    cases={'baseline':evaluate(Q(3,2),Q(1,3)),
      'load_matched':evaluate(Q(3,2),Q(20)),
      'joint_matched':evaluate(Q(3,32),Q(24),Q(1,4)),
      'reflection_control':evaluate(Q(30),Q(40))}
    a,b,c,d=[cases[k] for k in cases]
    assert abs(a['total']['incident']-c['total']['incident'])<1e-14
    assert b['terminal_over_net']>a['terminal_over_net']
    assert c['terminal_over_incident']>b['terminal_over_incident']
    assert d['terminal_over_net']>c['terminal_over_net']
    assert d['terminal_over_incident']<a['terminal_over_incident']
    assert all(v['exact_energy_zero'] and not v['restored'] for v in cases.values())
    result=dict(status='PASS',scope='FINITE_PRESELECTED_CANDIDATES_NOT_GLOBAL_OPTIMUM',
       sympy=S.__version__,cases=cases,source_normalized=True,
       no_real_antenna_calibration=True,physical_efficiency_claim=False,ci=False)
    print(json.dumps(result,indent=2));return result

if __name__=='__main__':main()
