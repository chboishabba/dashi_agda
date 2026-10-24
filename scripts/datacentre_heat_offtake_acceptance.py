#!/usr/bin/env python3
"""Source-to-offtaker data-centre thermal acceptance fixture (stdlib).

Examples are synthetic; input CSV is NOT evidence of calibration or plant operation.
Cooling water assumed pure, cp=4.186 kJ/(kg K); glycol needs measured cp.
Heat-pump electricity is external to the data-centre for KPI purposes.
"""
from dataclasses import dataclass
from math import isclose
import argparse,csv,json,unittest

CP=4.186
@dataclass(frozen=True)
class Hour:
    it_mw:float
    overhead_mw:float
    rack_hot_c:float
    rack_cold_c:float
    coolant_kg_s:float
    direct_demand_mw:float
    direct_inlet_c:float
    direct_target_c:float
    high_demand_mw:float
    high_target_c:float

@dataclass(frozen=True)
class Plant:
    capture_fraction:float=.8
    pinch_c:float=5
    evap_approach_c:float=3
    condenser_approach_c:float=3
    second_law_eff:float=.45
    max_hp_electric_mw:float=3
    pipe_eff:float=.9

def dispatch(h,plant=Plant()):
    if min(h.it_mw,h.overhead_mw,h.coolant_kg_s,h.direct_demand_mw,h.high_demand_mw)<0 or h.it_mw==0:
        raise ValueError('invalid site electrical power or demand')
    if not h.rack_hot_c>h.rack_cold_c>-273.15: raise ValueError('invalid coolant temperature')
    if h.direct_target_c<h.direct_inlet_c: raise ValueError('direct demand is not heating')
    if not (0<=plant.capture_fraction<=1 and 0<plant.pipe_eff<=1 and
            0<plant.second_law_eff<=1 and plant.max_hp_electric_mw>=0 and
            min(plant.pinch_c,plant.evap_approach_c,plant.condenser_approach_c)>=0):
        raise ValueError('invalid plant configuration')
    site=h.it_mw+h.overhead_mw
    measured_loop_mw=h.coolant_kg_s*CP*(h.rack_hot_c-h.rack_cold_c)/1000
    # This contract declares the loop as IT-origin heat only; heat from
    # additional sources requires a different, metered control volume.
    if measured_loop_mw>h.it_mw+1e-6:
        raise ValueError('rack coolant calorimetry exceeds declared IT heat input')
    cap=min(h.it_mw*plant.capture_fraction, measured_loop_mw)
    direct_feasible=(h.rack_hot_c>=h.direct_target_c+plant.pinch_c and
                     h.rack_cold_c>=h.direct_inlet_c+plant.pinch_c)
    direct=min(cap,h.direct_demand_mw/plant.pipe_eff) if direct_feasible else 0.
    temp_ev=h.rack_cold_c-plant.evap_approach_c+273.15
    temp_cond=h.high_target_c+plant.condenser_approach_c+273.15
    cop=plant.second_law_eff*temp_cond/(temp_cond-temp_ev) if temp_cond>temp_ev>0 else 0
    if cop>1:
        hp_source=min(cap-direct, h.high_demand_mw/plant.pipe_eff*(cop-1)/cop,
                      plant.max_hp_electric_mw*(cop-1))
        hp_el=hp_source/(cop-1)
    else: hp_source=hp_el=0
    hp_hot=hp_source+hp_el
    reused=direct+hp_source
    delivery=(direct+hp_hot)*plant.pipe_eff
    net_loss=(direct+hp_hot)-delivery
    ambient=site-reused
    assert isclose(site+hp_el,ambient+delivery+net_loss,abs_tol=1e-8)
    assert delivery <= h.direct_demand_mw+h.high_demand_mw+1e-8
    assert -1e-9<=reused<=site+1e-9
    return dict(source_cap_mw=cap,source_boundary_mw=reused,
                delivered_mw=delivery,hp_electric_mw=hp_el,network_loss_mw=net_loss,
                ambient_reject_mw=ambient,cop=cop if hp_source else 0,
                direct_feasible=direct_feasible,hp_feasible=cop>1,
                site_mw=site,it_mw=h.it_mw,
                erf_candidate=reused/site,pue=site/h.it_mw)

def summary(hours,plant=Plant()):
    outcomes=[dispatch(h,plant) for h in hours]
    if not outcomes:raise ValueError('at least one hourly row required')
    energy={name:sum(x[name] for x in outcomes) for name in
            ('source_boundary_mw','delivered_mw','hp_electric_mw','network_loss_mw',
             'ambient_reject_mw','site_mw','it_mw')}
    site=energy['site_mw']; source=energy['source_boundary_mw']; it=energy['it_mw']
    return dict(hours=len(outcomes),energy_mwh=energy,pue=site/it,
                erf_candidate=source/site,ere_candidate=(1-source/site)*site/it,
                measurement_gates_unpaid=[
                  'meter calibration, cooling-medium composition and flow',
                  'heat exchanger UA, temperature profiles and pressure loss',
                  'vendor COP map, auxiliaries, partial loads and backup',
                  'hourly metered off-taker demand, pipe losses and price',
                  'acoustic spectra before/after including external chillers/pumps',
                  'water consumption, refrigerant, baseline and marginal grid carbon',
                  'ISO 30134-6 site boundary and independently auditable beneficial reuse'
                ])

def read_csv(path):
    with open(path,newline='',encoding='utf-8') as f:
        rdr=csv.DictReader(f)
        fields=set(Hour.__dataclass_fields__)
        if not fields.issubset(rdr.fieldnames or []):raise ValueError('missing columns '+str(fields-set(rdr.fieldnames or [])))
        return [Hour(**{k:float(row[k]) for k in fields}) for row in rdr]

class TestGate(unittest.TestCase):
    def setUp(self):
        self.h=Hour(10,2.5,42,32,200,2,25,35,8.4,75)
    def test_balance_and_erf(self):
        d=dispatch(self.h)
        self.assertAlmostEqual(d['source_cap_mw'],8)
        self.assertAlmostEqual(d['pue'],1.25)
        self.assertAlmostEqual(d['erf_candidate'],.64)
        self.assertGreater(d['delivered_mw'],0)
    def test_pinch_fail(self):
        h=Hour(10,2.5,40,32,200,2,25,38,8.4,75)
        d=dispatch(h)
        self.assertFalse(d['direct_feasible'])
    def test_zero_offtaker(self):
        h=Hour(10,2.5,42,32,200,0,25,35,0,75)
        d=dispatch(h)
        self.assertEqual(d['source_boundary_mw'],0)
        self.assertEqual(d['hp_electric_mw'],0)
    def test_high_lift_cop_reject(self):
        h=Hour(10,2.5,42,32,200,0,25,35,8.4,150)
        self.assertEqual(dispatch(h,Plant(second_law_eff=.1))['hp_electric_mw'],0)
    def test_network_loss_explicit(self):
        d=dispatch(self.h,Plant(pipe_eff=.8))
        self.assertGreater(d['network_loss_mw'],0)
        self.assertLess(d['delivered_mw'],d['source_boundary_mw']+d['hp_electric_mw'])
    def test_hourly_aggregate(self):
        s=summary([self.h]*24)
        self.assertEqual(s['hours'],24)
        self.assertAlmostEqual(s['energy_mwh']['site_mw'],300)
    def test_invalid_coolant_energy_source(self):
        with self.assertRaises(ValueError):
            dispatch(Hour(10,2.5,42,32,300,2,25,35,8.4,75))
    def test_invalid(self):
        with self.assertRaises(ValueError):dispatch(Hour(0,2.5,42,32,200,2,25,35,8.4,75))
        with self.assertRaises(ValueError):dispatch(Hour(10,2.5,30,32,200,2,25,35,8.4,75))

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--selftest',action='store_true')
    p.add_argument('--example',action='store_true')
    p.add_argument('--csv')
    a=p.parse_args()
    if a.selftest:
        t=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TestGate))
        if not t.wasSuccessful():raise SystemExit(1)
    if a.example:
        rows=[Hour(10,2.5,42,32,200,2,25,35,8.4,75) for _ in range(24)]
    elif a.csv:rows=read_csv(a.csv)
    elif not a.selftest:p.error('choose --example, --csv or --selftest')
    else:return
    print(json.dumps(summary(rows),indent=2))

if __name__=='__main__':main()
