#!/usr/bin/env python3
"""C×D independent finite-energy LC circulation and recovery receiver.
A lossless normalized LC energy rotation is followed by explicitly dissipative
ring loss and extraction. The kick is a metered independent external energy
addition, never a free source. This is an exact discrete passivity benchmark,
NOT the topology or resonance frequency of the original V2.
"""
from dataclasses import dataclass,asdict
import math,json
from pathlib import Path

@dataclass(frozen=True)
class LC:
    L_h:float=.04
    C_f:float=10e-6
    external_kick_j:float=.1
    passive_ring_survival:float=.98
    extraction_fraction:float=.5
    converter_efficiency:float=.95
    controller_per_cycle_j:float=.002

    def validate(self):
        if self.L_h<=0 or self.C_f<=0 or self.external_kick_j<0 or self.controller_per_cycle_j<0:raise ValueError('invalid components/work')
        if not (0<=self.passive_ring_survival<=1 and 0<=self.extraction_fraction<=1 and 0<=self.converter_efficiency<=1):
            raise ValueError('energy partition cannot create energy')


def rotation_state(q_flux:float,q_charge:float,angle:float)->tuple[float,float]:
    """Normalized flux/charge rotation preserves x²+y² exactly in real arithmetic."""
    c=math.cos(angle);s=math.sin(angle)
    return c*q_flux-s*q_charge,s*q_flux+c*q_charge


def cycle(config:LC, stored_start_j:float,phase_rad:float=0.)->dict:
    config.validate()
    if stored_start_j<0:raise ValueError('negative energy state')
    # At each cycle the source injects exactly k J. Phase changes the split
    # between normalized modes but not the total conserved energy.
    q0=math.sqrt(2*(stored_start_j+config.external_kick_j))
    a,b=rotation_state(q0,0.,phase_rad)
    energy_after_rotation=(a*a+b*b)/2
    line_loss=energy_after_rotation*(1-config.passive_ring_survival)
    after_ring=energy_after_rotation-line_loss
    extraction=after_ring*config.extraction_fraction
    kept=after_ring-extraction
    load_output=extraction*config.converter_efficiency-config.controller_per_cycle_j
    converter_heat=extraction*(1-config.converter_efficiency)+config.controller_per_cycle_j
    residual=(stored_start_j+config.external_kick_j)-kept-load_output-line_loss-converter_heat
    return dict(start_j=stored_start_j,external_source_j=config.external_kick_j,
                stored_final_j=kept,stored_delta_j=kept-stored_start_j,
                line_loss_j=line_loss,converter_loss_j=converter_heat,
                recovered_available_j=extraction,useful_net_j=load_output,
                energy_residual_j=residual,phase_rad=phase_rad)


def periodic(config:LC)->dict:
    config.validate()
    retention=config.passive_ring_survival*(1-config.extraction_fraction)
    if retention>=1:
        return dict(steady_state_identifiable=False,reason='no storage decay, no unique forced periodic energy')
    initial=retention*config.external_kick_j/(1-retention)
    r=cycle(config,initial)
    assert abs(r['stored_delta_j'])<1e-12
    assert abs(r['energy_residual_j'])<1e-12
    assert r['useful_net_j']<=config.external_kick_j
    return dict(steady_state_identifiable=True,start_energy_j=initial,
                period_multiplier=retention,steady=r,
                interpretation='passive periodic energy partition; physically source driven, no V2 resonance identification')


def run()->dict:
    base=LC()
    cases={
        'ordinary_lossy_clamp':LC(extraction_fraction=.30,converter_efficiency=.8,controller_per_cycle_j=.001),
        'resonant_retention':LC(passive_ring_survival=.995,extraction_fraction=.30,converter_efficiency=.8,controller_per_cycle_j=.001),
        'enhanced_extraction':LC(extraction_fraction=.60,converter_efficiency=.95,controller_per_cycle_j=.002),
        'high_overhead':LC(extraction_fraction=.60,converter_efficiency=.95,controller_per_cycle_j=.06),
    }
    return dict(schema='dashi.v2.CD.LC-passive-recovery.v1',
        source='Constructed dimensionless normalised LC; not original V2',
        physical_reference={'L_h':base.L_h,'C_f':base.C_f,'natural_frequency_hz':1/(2*math.pi*math.sqrt(base.L_h*base.C_f))},
        cases={k:dict(params=asdict(v),result=periodic(v)) for k,v in cases.items()})

if __name__=='__main__':
    x=run();out=Path(__file__).resolve().parents[1]/'Artifacts/v2_lc_recovery_tranche_20261116.json';out.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v['result']['steady']['useful_net_j'] for k,v in x['cases'].items()},indent=2))
