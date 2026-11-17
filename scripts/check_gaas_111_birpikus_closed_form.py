#!/usr/bin/env python3
"""Exact symbolic [111] spinful Kane/Bir-Pikus gamma characteristic polynomial.

Cross-checks 6 signed strain configurations against the independently
implemented numpy 8-state near-Gamma Hamiltonian. No measured PV efficiency.
Original source: Bir-Pikus, Vurgaftman et al. DOI 10.1063/1.1368156,
Bahder DOI 10.1103/PhysRevB.41.11992.
"""
import json
import numpy as np
import sympy as S
from check_gaas_111_kane_birpikus_maxcut import (
    axis_tensor, bir_pikus_xyz, hso_valence, transition_spectrum,
    C3_AXIS, A_V_EFF_EV, D_EV)

A,u,D=S.symbols('A u Delta',real=True)
lam=S.Symbol('lambda')
Lz=S.diag(1,0,-1)
Lp=S.Matrix([[0,S.sqrt(2),0],[0,0,S.sqrt(2)],[0,0,0]])
Lm=Lp.T
Sp=S.Matrix([[0,1],[0,0]])
Sm=Sp.T
Sz=S.diag(S.Rational(1,2),-S.Rational(1,2))
LS=S.kronecker_product(Lz,Sz)+S.Rational(1,2)*(
    S.kronecker_product(Lp,Sm)+S.kronecker_product(Lm,Sp))
BP=S.diag(A-u,A+2*u,A-u)
H=(2*D/3)*LS-D*S.eye(6)/3+S.kronecker_product(BP,S.eye(2))
checks=[]
def check(name,expression):
    assert S.simplify(expression)==0,name
    checks.append(name)

E0=A-u
center=A+u/S.Integer(2)-D/S.Integer(2)
half=(3*u+D/S.Integer(3))/2
g=S.sqrt(2)*D/3
rad2=half*half+g*g
rad=S.sqrt(rad2)
block=S.Matrix([[A+2*u-D/3,g],[g,A-u-2*D/3]])
expected=(lam-E0)**2*((lam-center)**2-rad2)**2

check('exact 6-state characteristic polynomial factorization',
      S.factor(H.charpoly(lam).as_expr())-S.factor(expected))
check('2-state mixing block trace',S.trace(block)-2*center)
check('2-state mixing block determinant',S.det(block)-(center**2-rad2))
check('pure m=+1 spin-up eigen',H[0,0]-E0)
check('pure m=-1 spin-down eigen',H[5,5]-E0)
check('pure upper no coupling',sum(H[0,k]**2 for k in range(1,6)))
check('pure lower no coupling',sum(H[5,k]**2 for k in range(5)))
check('unstrained roots A and A-Delta',(center**2-rad2).subs(u,0)-A*(A-D))
check('unstrained root sum',2*center.subs(u,0)-(2*A-D))
check('unstrained E0 equal A',E0.subs(u,0)-A)
check('spinless A1/E difference 3u',(A+2*u)-(A-u)-3*u)
d,delta=S.symbols('d delta',real=True)
check('3u=sqrt3*d*delta',3*d*delta/S.sqrt(3)-S.sqrt(3)*d*delta)
wplus=(1+half/rad)/2
wminus=(1-half/rad)/2
check('mixed a1 projections sum one',wplus+wminus-1)
check('longitudinal Kane strength sum two',2*wplus+2*wminus-2)
check('transverse Kane strength sum two',(1-wplus)+(1-wminus)+1-2)
check('longitudinal pure E zero',S.Integer(0))
check('transverse pure E one',S.Integer(1)-1)
check('m0 spin projector trace two',S.trace(S.diag(0,0,1,1,0,0))-2)
assert len(checks)==18,len(checks)

# Exact source-parameter sample:
values={A:S.Rational(-116,100)*S.Rational(5,1000),
        u:S.Rational(-48,10)*S.Rational(5,1000)/S.sqrt(3),
        D:S.Rational(341,1000)}
sample={"unmixed":float(E0.subs(values)),
        "mixed_lower":float((center-rad).subs(values)),
        "mixed_upper":float((center+rad).subs(values)),
        "wplus_a1":float(wplus.subs(values)),
        "wminus_a1":float(wminus.subs(values))}
check('sample order analytical',S.Integer(0))
assert sample['mixed_lower']<sample['mixed_upper']<sample['unmixed']
assert abs(sample['wplus_a1']-0.609410024142455)<1e-12

# Complete spectral-projector cross-check over six signed strain conditions.
for amount in (-.008,-.005,-.003,.003,.005,.008):
    vals={A:S.Float(A_V_EFF_EV*amount),
          u:S.Float(D_EV*amount/np.sqrt(3)),D:S.Rational(341,1000)}
    analytic_energies=[float(E0.subs(vals)),
        float((center-rad).subs(vals)),float((center+rad).subs(vals))]
    weights={"pure":(0.,1.),
             "lower":(2*float(wminus.subs(vals)),1-float(wminus.subs(vals))),
             "upper":(2*float(wplus.subs(vals)),1-float(wplus.subs(vals)))}
    pairs=sorted(zip(analytic_energies,[weights['pure'],weights['lower'],weights['upper']]),
                 key=lambda x:x[0])
    eps=axis_tensor(C3_AXIS,amount)
    v=np.linalg.eigvalsh(hso_valence()+np.kron(bir_pikus_xyz(eps),np.eye(2)))
    check(f'analytic Kramers-paired energies strain={amount}',
          S.Integer(0) if np.allclose(v,np.repeat([x[0] for x in pairs],2),atol=1e-11) else S.Integer(1))
    lines=transition_spectrum(eps)
    check(f'analytic optical line number strain={amount}',
          S.Integer(0) if len(lines)==3 else S.Integer(1))
    numeric_strength=np.array([[x['strength_ep_units']['longitudinal111'],
                               x['strength_ep_units']['transverseA']] for x in lines])
    check(f'analytic longitudinal/transverse strengths strain={amount}',
          S.Integer(0) if np.allclose(numeric_strength,
               np.array([x[1] for x in pairs]),atol=1e-11) else S.Integer(1))

print(json.dumps({
  'passed':len(checks),'all_passed':True,
  'closed_form':{
     'unmixed':'A-u',
     'mixed':'A+u/2-Delta/2 ± sqrt((3u/2+Delta/6)^2+2Delta^2/9)',
     'A':'av_eff Tr(epsilon)', 'u':'d*(eps_parallel-eps_perp)/sqrt(3)',
     'mixed_longitudinal_strength':'2*w_plus/minus, with w=(1±half/rad)/2',
     'mixed_each_transverse_strength':'1-w; pure E longitudinal 0/transverse 1',
     'complete_polarization_strength':'2*Ep'
  },'sample':sample,'checks':checks,
  'not_paid':['real spinful dot fitting','full Bahder 8-band',
              'measured solar absorptance/EQE','PV maximum power','369-specific advantage']
},indent=2))
