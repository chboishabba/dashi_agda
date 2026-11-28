#!/usr/bin/env python3
"""LXXXVI: direct donor-import two-cell, two-port Maxwell/ADE acceptance.

The original Maxwell-Lorentz generator/midpoint/work auditor are imported rather
than copied. Synthetic inputs only; no external receiver E/H, source gain,
Poynting reflection, SI calibration, J18 port mapping, or physical admission.
No CI.
"""
import json
import sympy as S
from smith_filsinger_lorentz_ade_sympy import (
    generator, exact_midpoint, synthetic_cycle_work_receipt,
    LorentzMaterial, curl_matrix)

Q=S.Rational
N=2; DT=Q(1,10); G=Q(1,3)
A,B,M=generator(n=N,material=LorentzMaterial(),load_conductance=G)
assert A.shape==(8,8) and B.shape==(8,2)
assert curl_matrix(2)==S.Matrix([[1,-1],[0,1]])
assert S.simplify(M*A+A.T*M+S.diag(
    *([2*(Q(1,5)+G)]*N+[0]*N+[0]*N+[Q(8,9)]*N)))==S.zeros(8)

def run(natural,controller):
    assert len(natural)==len(controller)==4
    z=S.zeros(8,1);steps=[];volt=[];load_cell1=S.Integer(0)
    for ni,ci in zip(natural,controller):
        jn=S.Matrix([Q(ni),0]);jc=S.Matrix([0,Q(ci)])
        step=exact_midpoint(z,jn,jc,DT,A,B,M,load_conductance=G)
        assert step['residual']==0
        e=step['mid'][:2,:]
        volt.append(e[1])
        load_cell1+=S.expand(DT*G*e[1]*e[1])
        steps.append(step);z=step['z']
    work=synthetic_cycle_work_receipt(S.zeros(8,1),steps,M)
    assert work['conservation_residual']==0
    assert S.simplify(work['useful_load']-load_cell1)>=0
    assert not work['original_source_meter_present']
    return z,volt,work,S.expand(load_cell1)

# The one-step arrival delay is a model assumption, NOT an ionospheric Green.
launch=(1,0,0,1);arrival=(0,1,0,0);controller=(0,0,1,0)
assert arrival[0]==0 and arrival[1]==launch[0]
final,volt,work,terminal_load=run(arrival,controller)
assert not work['restored_all_4n_states']
assert run((0,)*4,(0,)*4)[0]==S.zeros(8,1)
vnat=S.Matrix(run(arrival,(0,)*4)[1])
vctrl=S.Matrix(run((0,)*4,controller)[1])
H=S.Matrix.hstack(vnat,vctrl)
assert H.rank()==2
assert S.Matrix.hstack(vnat,vnat).rank()==1
an,ac=S.symbols('natural_amplitude controller_amplitude',real=True)
assert [S.simplify(t) for t in (H.T*H).inv()*H.T*(H*S.Matrix([an,ac]))]==[an,ac]
gain,scale=S.symbols('gain scale',nonzero=True)
assert S.simplify(gain*an-gain/scale*(scale*an))==0
assert work['natural_work']+work['controller_work']==(
    work['useful_load']+work['ohmic_loss']+
    work['relaxation_loss']+work['storage_delta'])

result=dict(status='PASS',scope='EXACT_TWO_CELL_NATIVE_DONOR_IMPORTED_SYNTHETIC',
    donor='scripts/smith_filsinger_lorentz_ade_sympy.py',
    cells=2,steps=4,rank_independent=H.rank(),rank_collinear=1,
    exact_inverse=True,zero_source_zero_state=True,
    conservation_residual=str(work['conservation_residual']),
    natural_work=str(work['natural_work']),
    controller_work=str(work['controller_work']),
    total_load=str(work['useful_load']),
    terminal_cell1_load=str(terminal_load),
    other_cell_load=str(S.expand(work['useful_load']-terminal_load)),
    ohmic_loss=str(work['ohmic_loss']),
    relaxation_loss=str(work['relaxation_loss']),
    storage_delta=str(work['storage_delta']),
    receiver_voltage=[str(x) for x in volt],
    restored=False,physical_source_meter_present=False,
    source_gain_nonidentifiable=True,
    physical_antenna_impedance=False,reflected_wave_measured=False,
    calibrated_SI=False,j18_port_mapped=False,
    source_to_receiver_physical_admission=False,ci=False)
print(json.dumps(result,indent=2))
