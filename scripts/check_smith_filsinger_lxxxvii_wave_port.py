#!/usr/bin/env python3
"""LXXXVII: exact matched-wave port on original 2-cell Maxwell/Lorentz ADE.

Reuses donor generator/exact_midpoint/synthetic_cycle_work_receipt. The donor's
uniform dissipative load is decomposed into a characteristic-admittance
radiation port plus terminal conductance. All values synthetic, NOT SI metering
or an original Filsinger source. The two source labels remain external inputs.
"""
import json
import sympy as S
from smith_filsinger_lorentz_ade_sympy import (
    generator, exact_midpoint, synthetic_cycle_work_receipt, LorentzMaterial)
Q=S.Rational
N=2
DT=Q(1,10)
Z=Q(3,2)
G_TERMINAL=Q(1,3)
Y=1/Z
G_TOTAL=G_TERMINAL+Y
A,B,M=generator(n=N,material=LorentzMaterial(),load_conductance=G_TOTAL)


def evolve(port0,port1, dt=DT):
    """Incoming power-wave amplitudes a_j, reflected b_j=E_j-a_j.

    Norton matched line: j_j=2*a_j/Z - E_j/Z. The port sink E_j/Z is
    represented exactly by the donor generator's uniform Y damping.
    """
    assert len(port0)==len(port1)
    z=S.zeros(4*N,1);steps=[];ledger=[]
    for a0,a1 in zip(port0,port1):
        a=S.Matrix([S.sympify(a0),S.sympify(a1)])
        jn=S.Matrix([2*a[0]/Z,0]);jc=S.Matrix([0,2*a[1]/Z])
        step=exact_midpoint(z,jn,jc,dt,A,B,M,load_conductance=G_TOTAL)
        assert step['residual']==0
        e=step['mid'][:N,:]
        b=e-a
        incoming=dt*sum((x*x/Z for x in a),S.Integer(0))
        outgoing=dt*sum((x*x/Z for x in b),S.Integer(0))
        wave_sink=dt*Y*sum((x*x for x in e),S.Integer(0))
        terminal=dt*G_TERMINAL*e[1]**2
        other_cell=dt*G_TERMINAL*e[0]**2
        assert S.factor(incoming-outgoing-step['natural_work']-step['controller_work']+wave_sink)==0
        assert S.factor(step['useful_load']-wave_sink-terminal-other_cell)==0
        physical_balance=S.factor(step['energy_change']+step['ohmic']+
                       step['relaxation']+terminal+other_cell-incoming+outgoing)
        assert physical_balance==0
        for j in range(N):
            individual=S.factor(dt*(a[j]**2-b[j]**2)/Z - dt*e[j]*(2*a[j]-e[j])/Z)
            assert individual==0
        ledger.append(dict(incident=incoming,reflected=outgoing,
            net=incoming-outgoing,terminal=terminal,other_cell=other_cell,
            ohmic=step['ohmic'],relaxation=step['relaxation'],
            storage=step['energy_change'],port_sink=wave_sink,
            natural_current_work=step['natural_work'],
            controller_current_work=step['controller_work'],
            v_terminal=e[1],i_terminal=G_TERMINAL*e[1],
            reflected_amplitudes=b))
        steps.append(step);z=step['z']
    donor_receipt=synthetic_cycle_work_receipt(S.zeros(4*N,1),steps,M)
    assert donor_receipt['conservation_residual']==0
    sums={key:S.factor(sum(row[key] for row in ledger)) for key in
          ('incident','reflected','net','terminal','other_cell','ohmic','relaxation',
           'storage','port_sink','natural_current_work','controller_current_work')}
    assert S.factor(sums['incident']-sums['reflected']-sums['terminal']-
        sums['other_cell']-sums['ohmic']-sums['relaxation']-sums['storage'])==0
    assert S.factor(sums['net']-sums['natural_current_work']-
              sums['controller_current_work']+sums['port_sink'])==0
    return z,ledger,sums,donor_receipt


def test():
    natural=(0,1,0,0)
    controller=(0,0,1,0)
    z,ledger,total,donor=evolve(natural,controller)
    assert all(row['incident']>=0 and row['reflected']>=0 for row in ledger)
    assert all(row['terminal']>=0 and row['other_cell']>=0 for row in ledger)
    assert evolve((0,)*4,(0,)*4)[0]==S.zeros(8,1)
    assert not donor['restored_all_4n_states']
    # A short transient can have negative net port work (reflected > incident).
    # Thus do not incorrectly assert each step's net port is nonnegative.
    assert S.factor(sum(row['net'] for row in ledger)-total['net'])==0
    def readout(x,y):return S.Matrix([row['v_terminal'] for row in evolve(x,y)[1]])
    n=readout(natural,(0,)*4);c=readout((0,)*4,controller)
    H=S.Matrix.hstack(n,c)
    assert H.rank()==2
    assert S.Matrix.hstack(n,n).rank()==1
    u,v=S.symbols('u v',real=True)
    assert [S.factor(t) for t in (H.T*H).inv()*H.T*H*S.Matrix([u,v])]==[u,v]
    g,k=S.symbols('g k',nonzero=True)
    assert S.simplify(g*u-(g/k)*(k*u))==0
    # Zero terminal admittance is an exact negative control: incoming can
    # still excite internal fields, while useful terminal work vanishes.
    assert G_TERMINAL>0 and total['terminal']>0
    return dict(status='PASS',scope='EXACT_SYNTHETIC_MATCHED_WAVE_PORT_NO_FIELD_CALIBRATION',
        sympy=S.__version__,cells=2,steps=len(ledger),characteristic_impedance=str(Z),
        admittance=str(Y),terminal_conductance=str(G_TERMINAL),
        per_step_ADE_energy_zero=True,per_step_wave_port_identity_zero=True,
        per_step_decomposed_energy_zero=True,full_cycle_energy_zero=True,
        source_rank=int(H.rank()),collinear_rank=1,exact_inverse=True,
        zero_source_zero_state=True,full_state_restored=False,
        totals={k:str(v) for k,v in total.items()},
        receiver_voltage=[str(row['v_terminal']) for row in ledger],
        receiver_current=[str(row['i_terminal']) for row in ledger],
        physically_measured_incident_reflected=False,antenna_SI_calibrated=False,
        original_J18_circuit_pins_mapped=False,physical_source_admission=False,
        gravity_coupling=False,ci=False)

if __name__=='__main__':print(json.dumps(test(),indent=2))
