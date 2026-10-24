#!/usr/bin/env python3
"""Source-to-offtaker data-centre thermal acceptance fixture (stdlib).

Examples are synthetic; input CSV is NOT evidence of calibration or plant operation.
Cooling water assumed pure, cp=4.186 kJ/(kg K); glycol needs measured cp.
Heat-pump electricity is external to the data-centre for KPI purposes.
"""
from dataclasses import dataclass
from math import isclose, isfinite
import argparse,csv,json,unittest
from datetime import datetime,timedelta,timezone

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
    readings=tuple(getattr(h,k) for k in Hour.__dataclass_fields__)
    settings=tuple(getattr(plant,k) for k in Plant.__dataclass_fields__)
    if not all(isfinite(x) for x in readings+settings):
        raise ValueError('non-finite site, sensor, demand or plant reading')
    if min(h.direct_inlet_c,h.direct_target_c,h.high_target_c)<=-273.15:
        raise ValueError('nonphysical receiver temperature')
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
    if not isclose(site+hp_el,ambient+delivery+net_loss,abs_tol=1e-8):
        raise ValueError('whole-system first-law violation')
    if delivery > h.direct_demand_mw+h.high_demand_mw+1e-8:
        raise ValueError('delivery exceeds declared offtake')
    if not -1e-9<=reused<=site+1e-9:
        raise ValueError('invalid reuse and source boundary')
    return dict(source_cap_mw=cap,source_boundary_mw=reused,
                delivered_mw=delivery,hp_electric_mw=hp_el,network_loss_mw=net_loss,
                ambient_reject_mw=ambient,cop=cop if hp_source else 0,
                direct_feasible=direct_feasible,hp_feasible=cop>1,
                site_mw=site,it_mw=h.it_mw,
                erf_candidate=reused/site,pue=site/h.it_mw)

def alternate_hp_meter_boundary(d):
    """Pure accounting thought experiment: relocate HP meter inside facility.

    Assumes all exported heat qualifies as useful reuse at the handoff point.
    Pipeline loss, downtime, legal meter layout and offsite use still need audits.
    """
    site,source,drive,it=(d['site_mw'],d['source_boundary_mw'],
                          d['hp_electric_mw'],d['it_mw'])
    internal_pue=(site+drive)/it
    internal_erf=(source+drive)/(site+drive)
    internal_ere=(1-internal_erf)*internal_pue
    external_ere=(1-source/site)*(site/it)
    if not isclose(internal_ere,external_ere,abs_tol=1e-10):
        raise ValueError('boundary reassignment violated ideal ERE accounting')
    return dict(external_pue=site/it,external_erf_candidate=source/site,
                internal_pue=internal_pue,internal_erf_candidate=internal_erf,
                unchanged_ideal_ere=external_ere)

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
    """Reject unmapped or unaligned records; IDs are claims, not verified receipts."""
    with open(path,newline='',encoding='utf-8') as f:
        rdr=csv.DictReader(f)
        fields=set(Hour.__dataclass_fields__)
        provenance={'timestamp_utc','source_site_id','offtaker_id',
                    'source_meter_id','offtaker_meter_id','calibration_receipt_ref'}
        missing=(fields|provenance)-set(rdr.fieldnames or [])
        if missing:raise ValueError('missing hourly columns '+str(sorted(missing)))
        rows=list(rdr)
    if not rows:raise ValueError('no recorded hours')
    initial=None
    previous=None
    records=[]
    for row in rows:
        ids=tuple(row[x].strip() for x in sorted(provenance-{'timestamp_utc'}))
        if not all(ids):raise ValueError('empty site, meter, or calibration provenance')
        if initial is None: initial=ids
        if initial!=ids:raise ValueError('cross-site, cross-meter or changed calibration join')
        dt=datetime.fromisoformat(row['timestamp_utc'].replace('Z','+00:00'))
        if dt.tzinfo is None or dt.utcoffset()!=timedelta(0):
            raise ValueError('timestamp_utc must be explicitly in UTC')
        if previous is not None and dt-previous!=timedelta(hours=1):
            raise ValueError('nonconsecutive, repeated or missing UTC hourly bin')
        previous=dt
        records.append(Hour(**{k:float(row[k]) for k in fields}))
    return records

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

    def test_hp_boundary_reassignment(self):
        d=dispatch(self.h)
        b=alternate_hp_meter_boundary(d)
        self.assertGreater(b['internal_pue'],b['external_pue'])
        self.assertGreater(b['internal_erf_candidate'],b['external_erf_candidate'])
        self.assertAlmostEqual(b['unchanged_ideal_ere'],.45)
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

    def test_csv_requires_original_provenance(self):
        import tempfile, os
        fd,path=tempfile.mkstemp(suffix='.csv')
        try:
            with os.fdopen(fd,'w') as o:
                o.write(','.join(Hour.__dataclass_fields__)+'\n')
                o.write(','.join(['10','2.5','42','32','200','2','25','35','8.4','75'])+'\n')
            with self.assertRaises(ValueError):read_csv(path)
        finally:os.unlink(path)
    def test_csv_valid_aligned_pair_and_duplicate_rejection(self):
        import tempfile, os
        meta=dict(source_site_id='SYNTHETIC_SITE',
                  offtaker_id='SYNTHETIC_CUSTOMER',
                  source_meter_id='TEST_SOURCE_METER',
                  offtaker_meter_id='TEST_DEMAND_METER',
                  calibration_receipt_ref='UNVERIFIED_TEST_RECEIPT')
        base=dict(self.h.__dict__,**meta)
        with tempfile.NamedTemporaryFile('w',newline='',suffix='.csv',
                                         delete=False) as f:
            path=f.name
            writer=csv.DictWriter(f,fieldnames=['timestamp_utc']+list(base))
            writer.writeheader()
            writer.writerow(dict(base,timestamp_utc='2026-10-24T10:00:00+00:00'))
            writer.writerow(dict(base,timestamp_utc='2026-10-24T11:00:00+00:00'))
        try:
            self.assertEqual(len(read_csv(path)),2)
            with open(path,'w',newline='') as f:
                writer=csv.DictWriter(f,fieldnames=['timestamp_utc']+list(base))
                writer.writeheader()
                writer.writerow(dict(base,timestamp_utc='2026-10-24T10:00:00+00:00'))
                writer.writerow(dict(base,timestamp_utc='2026-10-24T10:00:00+00:00'))
            with self.assertRaises(ValueError):read_csv(path)
        finally:os.unlink(path)
    def test_nonfinite_and_absolute_zero_rejected(self):
        from dataclasses import replace
        for h in [replace(self.h, rack_hot_c=float('nan')),
                  replace(self.h, direct_demand_mw=float('inf')),
                  replace(self.h, high_target_c=-274.)]:
            with self.assertRaises(ValueError):dispatch(h)
        for plant in [Plant(capture_fraction=float('nan')),
                      Plant(max_hp_electric_mw=float('inf'))]:
            with self.assertRaises(ValueError):dispatch(self.h,plant)
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
