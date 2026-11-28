#!/usr/bin/env python3
"""Exact rational, one-cell Maxwell--Lorentz ADE terminal/source test.
Transcribes the published native F13/F15 finite generator and implicit
midpoint equations, NOT a measured ionosphere or J18 impedance transfer.
"""
import json
import sympy as S

Q=S.Rational
A=S.Matrix([[-Q(1,10),Q(1,2),0,-Q(1,2)],
            [-Q(2,3),0,0,0],
            [0,0,0,1],
            [Q(3,2),0,-4,-Q(2,3)]])
B=S.Matrix([Q(1,2),0,0,0])
M=S.diag(2,Q(3,2),Q(8,3),Q(2,3))
assert S.simplify(M*A + A.T*M + S.diag(Q(2,5),0,0,Q(8,9))) == S.zeros(4)

def one_step(z, j_nat, j_ctrl, dt=Q(1,10), gl=Q(0)):
    # Rebuild A with explicit separately metered conductance in E equation.
    Ag=A.copy(); Ag[0,0]-=gl/2
    mid=(S.eye(4)-dt*Ag/2).inv()*(z+dt*B*(j_nat+j_ctrl)/2)
    end=2*mid-z
    e,h,p,v=mid
    initial=(z.T*M*z)[0]/2; final=(end.T*M*end)[0]/2
    nat=dt*e*j_nat;ctrl=dt*e*j_ctrl
    heat=dt*(Q(1,5)*e*e+Q(4,9)*v*v)
    load=dt*gl*e*e
    delta=S.expand(final-initial)
    assert S.simplify(nat+ctrl-heat-load-delta)==0
    return end, dict(natural=nat,controller=ctrl,heat=heat,load=load,delta=delta,
                     terminal_voltage=e,terminal_current=gl*e,
                     midpoint_e=e,midpoint_v=v)

def propagate(natural,controller,gl=Q(1,3)):
    assert len(natural)==len(controller)
    z=S.zeros(4,1);rows=[]
    for jn,jc in zip(natural,controller):
        z,row=one_step(z,jn,jc,gl=gl);rows.append(row)
    for row in rows:
        assert S.simplify(row['natural']+row['controller']-row['heat']-row['load']-row['delta'])==0
    return z,rows

def test():
    zero,rz=propagate([0,0,0],[0,0,0]);assert zero==S.zeros(4,1)
    assert all(all(v==0 for v in r.values()) for r in rz)
    n=[Q(1),Q(0),Q(1)];ctrl=[Q(0),Q(1),Q(0)]
    a,ra=propagate(n,[0,0,0]);b,rb=propagate([0,0,0],n)
    assert a==b # same current at same port cannot distinguish provenance
    for x,y in zip(ra,rb):
        assert x['terminal_voltage']==y['terminal_voltage']
    full,rows=propagate(n,ctrl)
    native_source_work=S.expand(sum(r['natural'] for r in rows))
    controller_work=S.expand(sum(r['controller'] for r in rows))
    useful=S.expand(sum(r['load'] for r in rows))
    losses=S.expand(sum(r['heat'] for r in rows))
    delta=S.expand(sum(r['delta'] for r in rows))
    assert S.simplify(native_source_work+controller_work-useful-losses-delta)==0
    assert useful>=0 and losses>=0
    # Source-to-field map linear in labelled current for same B; same pulse
    # produces indistinguishable columns. Distinct calibrated pulse shapes
    # give full rank in 3 independent midpoint samples.
    def ev(v):return S.Matrix([r['terminal_voltage'] for r in propagate(v,[0,0,0])[1]])
    coln=ev(n);colc=ev(ctrl)
    matched=S.Matrix.hstack(coln,coln)
    separated=S.Matrix.hstack(coln,colc)
    assert matched.rank()==1 and separated.rank()==2
    # Uncalibrated source field * unknown antenna/matching gain remains gauge.
    gain,current,scale=S.symbols('gain current scale',nonzero=True)
    assert S.simplify((gain/scale)*(scale*current)-gain*current)==0
    # J18 interface still has a separate physical, frequency/time/impedance map.
    return dict(status='PASS',scope='EXACT_RATIONAL_ONE_CELL_THREE_STEP_CONDITIONAL',
      steps=len(rows),source_profile_rank_same=matched.rank(),
      source_profile_rank_separated=separated.rank(),
      total_natural_work=str(native_source_work),controller_work=str(controller_work),
      total_useful_load=str(useful),total_heat=str(losses),
      total_storage_change=str(delta),
      terminal_voltage_trace=[str(r['terminal_voltage']) for r in rows],
      current_trace=[str(r['terminal_current']) for r in rows],
      zero_source_zero_output=True,energy_residual_exact_zero=True,
      actual_calibrated_input=False,j18_physical_port_weld=False,
      measured_physical_transfer=False,github_ci=False)

if __name__=='__main__':print(json.dumps(test(),indent=2))
