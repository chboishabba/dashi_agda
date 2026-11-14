#!/usr/bin/env python3
"""Source-attributed theoretical hydrogen/diesel cylinder sensitivity model.

User-directed question; ChatGPT-authored integration (2026-11-10).
Published data are owned by their original authors:
Estrada et al. (2022), DOI 10.1016/j.heliyon.2022.e09285: 78 mm bore,
62.57 mm stroke, 20:1 compression, H2 20 L/min, cell 13.45V, 15.1A.
Amatnieks et al. (2026), DOI 10.3390/en19173951: selected phasing
and pressure changes; NOT a calibration for the Estrada engine.
Single-zone first-law heat-release method: DOI 10.3390/en19071657;
Wiebe burn shape: DOI 10.3390/jmse8030204.
All non-reported gas, phasing, thermal and rod-length inputs are assumptions.
No McLaren/XFuel measurement or causal physical validation is implied.
"""
import math
import json
from dataclasses import dataclass, replace, asdict
import unittest

@dataclass(frozen=True)
class AssumedCylinder:
    bore_mm: float=78.0               # Estrada: measured geometry
    stroke_mm: float=62.57             # Estrada
    compression_ratio: float=20.0      # Estrada
    rod_crank_ratio: float=3.5         # ASSUMED
    gamma: float=1.35                 # ASSUMED CONSTANT
    p_bdc_bar: float=1.0              # ASSUMED
    q_apparent_j: float=400.0         # ASSUMED
    start_ca_deg: float=-10.0         # ASSUMED
    duration_ca_deg: float=50.0       # ASSUMED
    wiebe_a: float=5.0                # ASSUMED
    wiebe_m: float=2.0                # ASSUMED
    step_ca_deg: float=.1

def volume(theta, c):
    a=c.stroke_mm/2000
    r=c.bore_mm/2000
    rod=a*c.rod_crank_ratio
    swept=math.pi*r*r*2*a
    clearance=swept/(c.compression_ratio-1)
    t=math.radians(theta)
    distance=a*(1-math.cos(t))+rod-math.sqrt(rod*rod-a*a*math.sin(t)**2)
    return clearance+math.pi*r*r*distance

def burned_fraction(theta, c):
    u=(theta-c.start_ca_deg)/c.duration_ca_deg
    u=max(0.,min(1.,u))
    return 1.-math.exp(-c.wiebe_a*u**(c.wiebe_m+1))

def ca50(c):
    return c.start_ca_deg+c.duration_ca_deg*(math.log(2)/c.wiebe_a)**(1/(c.wiebe_m+1))

def integrate(c):
    """Ideal p-V compression/expansion; excludes walls, pumping and friction."""
    p=c.p_bdc_bar*1e5
    peak=p
    theta_peak=-180.
    work=0.
    total_steps=int(round(360./c.step_ca_deg))
    for k in range(total_steps):
        t0=-180.+k*c.step_ca_deg
        t1=t0+c.step_ca_deg
        tm=(t0+t1)/2
        v0,vm,v1=volume(t0,c),volume(tm,c),volume(t1,c)
        dq=c.q_apparent_j*(burned_fraction(t1,c)-burned_fraction(t0,c))
        p1=(p*(v0/vm)**c.gamma+(c.gamma-1)*dq/vm)*(vm/v1)**c.gamma
        work+=.5*(p+p1)*(v1-v0)
        if p1>peak:
            peak,theta_peak=p1,t1
        p=p1
    return dict(pressure_peak_bar=peak/1e5,pressure_peak_ca_deg=theta_peak,
                indicated_work_j=work,ca50_ca_deg=ca50(c),
                ideal_work_over_apparent_heat=work/c.q_apparent_j if c.q_apparent_j else None)

def power_discrepancy():
    h2_lhv_kw=(20/1000)*.0899*119.7e6/60/1000
    dc_kw=13.45*15.1/1000
    return dict(reported_flow_h2_lhv_kw=h2_lhv_kw,
                listed_dc_vi_kw=dc_kw,
                unreconciled_ratio=h2_lhv_kw/dc_kw)

def same_output(share,eta_ratio,electrolyser_eta=.70):
    # F/F0=(1-share)/r ; H/F0=share/r
    diesel=(1-share)/eta_ratio
    hydrogen=share/eta_ratio
    electricity=hydrogen/electrolyser_eta
    return dict(hydrogen_engine_share=share,relative_engine_efficiency=eta_ratio,
                baseline_diesel=1.,assisted_diesel=diesel,hydrogen=hydrogen,
                electrolysis_electricity=electricity,
                diesel_reduction_fraction=1-diesel,
                net_input_reduction_fraction=1-diesel-electricity)

class ExactRegressions(unittest.TestCase):
    def test_geometry(self):
        c=AssumedCylinder()
        self.assertAlmostEqual(volume(180,c)/volume(0,c),20.,places=10)
    def test_work_is_positive(self):
        self.assertGreater(integrate(AssumedCylinder())['indicated_work_j'],0)
    def test_angular_convergence(self):
        c=AssumedCylinder()
        a=integrate(replace(c,step_ca_deg=.2))['indicated_work_j']
        b=integrate(replace(c,step_ca_deg=.05))['indicated_work_j']
        self.assertLess(abs(a-b)/b,.005)
    def test_literature_input_reconciliation_flag(self):
        self.assertGreater(power_discrepancy()['unreconciled_ratio'],17)
    def test_same_output_thirty_percent(self):
        for share in (0.,.02,.05,.1,.18,.37):
            result=same_output(share,(1-share)/.7)
            self.assertAlmostEqual(result['diesel_reduction_fraction'],.3)
    def test_hydrogen_substitution_alone_is_energy_loss(self):
        self.assertLess(same_output(.1,1)['net_input_reduction_fraction'],0)
    def test_earlier_ca50(self):
        c=AssumedCylinder()
        self.assertAlmostEqual(ca50(c)-ca50(replace(c,start_ca_deg=c.start_ca_deg-3.5)),3.5)

if __name__=='__main__':
    tests=unittest.defaultTestLoader.loadTestsFromTestCase(ExactRegressions)
    if not unittest.TextTestRunner(verbosity=1).run(tests).wasSuccessful():
        raise SystemExit(1)
    base=AssumedCylinder()
    baseline=integrate(base)
    cases={
        'assumed_baseline':base,
        '3p5_deg_earlier_ca50_same_heat':replace(base,start_ca_deg=base.start_ca_deg-3.5),
        '3p5_deg_later_ca50_same_heat':replace(base,start_ca_deg=base.start_ca_deg+3.5),
        'duration_plus_46pct_same_heat':replace(base,duration_ca_deg=base.duration_ca_deg*1.46),
        'duration_minus_12p5pct_same_heat':replace(base,duration_ca_deg=base.duration_ca_deg*.875),
    }
    output={'provenance':__doc__,'reported_number_reconciliation':power_discrepancy(),
            'assumptions':asdict(base),'theoretical_cases':{},'energy_share_cases':[]}
    for label,c in cases.items():
        r=integrate(c)
        r['work_change_percent']=100*(r['indicated_work_j']/baseline['indicated_work_j']-1)
        output['theoretical_cases'][label]=r
    for share in (0,.02,.05,.1,.18,.37):
        output['energy_share_cases'].append(same_output(share,(1-share)/.7))
    print(json.dumps(output,indent=2))
