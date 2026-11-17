#!/usr/bin/env python3
"""A-H/Omega robust pulse/recovery Pareto cut, not a V2 hardware model.

Matched shaft power at every candidate. Same waveform for ordinary/enhanced
converter comparisons. Corner robustness of explicitly stated interval-box
uncertainties; *not* certification of switching silicon or all material states.
"""
from __future__ import annotations
from dataclasses import asdict, dataclass, replace
from pathlib import Path
import json, math
from v2_omega_smooth_storage_metrology_maxcut import Plant, profile

@dataclass(frozen=True)
class Uncertainty:
    resistance_increase_ohm:float=.03
    voltage_derating_v:float=2.
    unmodelled_voltage_demand_v:float=1.
    enhanced_eta_min:float=.985
    ordinary_eta_max:float=.955
    added_controller_overhead_max_w:float=.7

    def validate(self):
        if min(self.resistance_increase_ohm,self.voltage_derating_v,self.unmodelled_voltage_demand_v,self.added_controller_overhead_max_w)<0:
            raise ValueError('nonnegative uncertainty required')
        if not (0<self.ordinary_eta_max<=1 and 0<self.enhanced_eta_min<=1):
            raise ValueError('passive converter fractions required')


def point(q:float,lead:float,unc:Uncertainty=Uncertainty(),n:int=16384)->dict:
    unc.validate()
    base=Plant(n=n)
    corners=[]
    for rerror in (0.,unc.resistance_increase_ohm):
        for vderate in (0.,unc.voltage_derating_v):
            p=replace(base,R_ohm=base.R_ohm+rerror,Vlim_v=base.Vlim_v-vderate)
            # For lower bounded output and upper-bounded controller loss, use
            # explicitly specified conservative converter fractions.
            enhanced=profile(p,q,lead,eta_reverse=unc.enhanced_eta_min,
                             control_extra_w=unc.added_controller_overhead_max_w,
                             require_feasible=False)
            ordinary=profile(p,q,lead,eta_reverse=unc.ordinary_eta_max,
                             control_extra_w=0.,require_feasible=False)
            headroom=p.Vlim_v-enhanced['continuous_voltage_grid_lipschitz_upper_v']-unc.unmodelled_voltage_demand_v
            # The improvement is correlated on the very same coil waveform.
            gross=enhanced['gross_reverse_w']
            delta=(unc.enhanced_eta_min-unc.ordinary_eta_max)*gross-unc.added_controller_overhead_max_w
            integration_error=(unc.enhanced_eta_min-unc.ordinary_eta_max)*enhanced['coil_abs_power_lipschitz_upper_w_per_rad']*math.pi/n
            corners.append({'resistance_increase_ohm':rerror,'derating_v':vderate,
              'enhanced_net_bus_w':enhanced['net_bus_w'], 'ordinary_net_bus_w':ordinary['net_bus_w'],
              'required_voltage_upper_v':enhanced['continuous_voltage_grid_lipschitz_upper_v']+unc.unmodelled_voltage_demand_v,
              'continuous_voltage_headroom_v':headroom,
              'recovery_gain_lower_w':delta-integration_error,
              'shaft_w':enhanced['shaft_w'],
              'full_cycle_storage_by_manufactured_waveform':enhanced['windings_periodic_by_analytic_waveform'],
              'continuous_bus_enclosure_certified':enhanced['continuous_dc_bus_enclosure_certified'],
              'current_upper_a':enhanced['analytic_current_upper_a'],
              'slew_upper_a_s':enhanced['analytic_slew_upper_a_s']})
    rob=min(c['continuous_voltage_headroom_v'] for c in corners)
    gain=min(c['recovery_gain_lower_w'] for c in corners)
    status=(rob>=0 and gain>0 and all(c['continuous_bus_enclosure_certified'] for c in corners)
         and all(c['current_upper_a']<=base.Ilim_a and c['slew_upper_a_s']<=base.slew_lim_a_s for c in corners))
    return {'q':q,'lead_rad':lead,'uncertainty':asdict(unc),
      'corner_robust_winding_bus_certified':bool(status),
      'minimum_voltage_headroom_v':rob,'worst_enhanced_net_bus_w':min(c['enhanced_net_bus_w'] for c in corners),
      'worst_ordinary_net_bus_w':min(c['ordinary_net_bus_w'] for c in corners),
      'minimum_correlated_recovery_gain_lower_w':gain,
      'corners':corners,
      'scope':'Fixed waveform, passive averaged converter, interval-box corner search; no silicon or thermal verification'}


def run()->dict:
    u=Uncertainty()
    points=[point(q,lead,u) for q in (0.,.1,.2,.3,.4) for lead in (-.25,-.2,-.15,-.1,-.05,0.)]
    acceptable=[p for p in points if p['corner_robust_winding_bus_certified']]
    winner=max(acceptable,key=lambda p:p['worst_enhanced_net_bus_w']) if acceptable else None
    nominal=point(0.,0.,u)
    return {'schema':'DASHI.V2.Omega.robust-smooth-recovery.v1',
      'source_identified':False,'measured_V2_efficiency':False,
      'candidates':len(points),'robust_certified_count':len(acceptable),
      'winner':winner,'nominal_q0_lead0':nominal,
      'conditions':['Same hypothetical 45 W shaft work at every candidate',
       'All magnetic properties fixed except specified R interval',
       'Closed magnetic winding waveform and constructed bus capacitor cycle',
       'Same current and shaft waveform in ordinary and enhanced arms',
       'Continuous bounds are conservative sufficient conditions, not necessity',
       'No pointwise switching/deadtime/thermal or source-selected hardware model'],
      'open_gates':['physical converter efficiency map over forward/reverse current/voltage/temperature',
       'actual switching ripple and DC bus under closed-loop current tracking',
       'global continuous-control optimisation and material uncertainty',
       'measured V2 motor efficiency, actual generator torque and all-port sources',
       'Agda kernel and full original P0-P4 strict gates']}

if __name__=='__main__':
    r=run()
    path=Path(__file__).resolve().parents[1]/'Artifacts/v2_omega_robust_pulse_recovery_20261117.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({'candidates':r['candidates'],'robust_certified_count':r['robust_certified_count'],
                      'winner':{k:v for k,v in (r['winner'] or {}).items() if k!='corners'},
                      'nominal_robust':r['nominal_q0_lead0']['corner_robust_winding_bus_certified']},indent=2))
