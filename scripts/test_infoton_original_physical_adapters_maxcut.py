#!/usr/bin/env python3
"""Same-source physical metrology and gauge-no-go tests; no fake hardware data."""
import sys
import unittest
from dataclasses import replace
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import infoton_original_physical_adapters_maxcut as p


class PhysicalAdapterMaxCut(unittest.TestCase):
    def test_real_sm_charge_adapter(self):
        r = p.original_charge_receipt()
        self.assertEqual((r['up_sixths'], r['down_sixths'],
                          r['electron_sixths'], r['neutrino_sixths']), (4,-2,-6,0))
        self.assertFalse(r['original_27_physical_theorem_claimed_here'])

    def test_conditional_global_charge(self):
        self.assertTrue(all(p.global_u3_charge_residue(p.CHARGE_SIXTHS[n],
                                                     p.COLOUR_TRIALITY[n]) for n in p.CHARGE_SIXTHS))
        self.assertFalse(p.global_u3_charge_residue(1,1))
        self.assertFalse(p.global_u3_charge_residue(4,0))

    def test_fermi_anchor_all_temperatures(self):
        for t in ['0.01','4','300','310','100000']:
            self.assertEqual(p.fermi_landauer_anchor(Decimal(t)),
                             (Fraction(1,3),Fraction(2,3)))
        self.assertNotEqual(p.CHARGE_SIXTHS['up'],p.CHARGE_SIXTHS['down'])

    def test_FD_only_not_charge_mapping(self):
        data = [(k,p.fermi_landauer_anchor(Decimal(300))[0], v)
                for k,v in p.CHARGE_SIXTHS.items()]
        self.assertEqual(len(set(occ for _,occ,_ in data)),1)
        self.assertGreater(len(set(charge for _,_,charge in data)),1)

    def test_mass_reference_and_temp_scaling(self):
        x = p.landauer_mass_equivalent_kg(Decimal(300))
        y = p.landauer_mass_equivalent_kg(Decimal(310))
        self.assertTrue(Decimal('3.0e-38') < x < Decimal('3.4e-38'))
        self.assertAlmostEqual(float(y/x),31/30)

    def test_mass_is_not_fixed_particle(self):
        self.assertNotEqual(p.landauer_mass_equivalent_kg(Decimal(300)),
                            p.landauer_mass_equivalent_kg(Decimal(310)))

    def test_reversible_operation_has_no_forced_erase_floor(self):
        self.assertEqual(p.landauer_erasure_floor_joule(Decimal(300),0),0)
        self.assertGreater(p.landauer_erasure_floor_joule(Decimal(300),1),0)

    def test_invalid_thermal_inputs(self):
        for v in ('0','-1','Infinity','NaN'):
            with self.assertRaises(ValueError): p.fermi_landauer_anchor(Decimal(v))
        with self.assertRaises(ValueError): p.landauer_erasure_floor_joule(Decimal(300),-1)

    def test_130kw_rack_sensitivity(self):
        self.assertEqual(p.source_rack_sensitivity_kw(Fraction(1)),130)
        self.assertAlmostEqual(float(p.source_rack_sensitivity_kw(Fraction(0))),130*163/12264)
        self.assertGreater(float(p.source_rack_sensitivity_kw(Fraction(1,4))),33)

    def fixture(self):
        return p.MeasuredVerifiedService(
            source_receipt='synthetic-not-physical', workload_sha256='same-work',
            fault_corpus_sha256='same-fault-corpus', implementation_sha='baseline',
            hardware_id='same-platform', calibration_receipt='synthetic-mock',
            timestamp_utc='2026-11-16T00:00Z', verified_outputs=10,
            measured_joules=Decimal(100),measured_duration_s=Decimal(10),
            error_correction_proof_receipt='synthetic-reference-only')

    def test_matched_synthetic_energy(self):
        a = self.fixture(); b = replace(a, implementation_sha='proposed',measured_joules=Decimal(80))
        x = p.compare_measured_verified_service(a,b)
        self.assertEqual(x['ratio'],Decimal('1.25'))
        self.assertEqual(x['energy_reduction_fraction'],Decimal('0.2'))
        self.assertFalse(x['independent_meter_authentication'])

    def test_mismatched_workload_rejected(self):
        a = self.fixture(); b = replace(a, workload_sha256='different')
        with self.assertRaisesRegex(ValueError,'workload'):p.compare_measured_verified_service(a,b)

    def test_mismatched_faults_rejected(self):
        a = self.fixture(); b = replace(a, fault_corpus_sha256='different')
        with self.assertRaisesRegex(ValueError,'fault'):p.compare_measured_verified_service(a,b)

    def test_mismatched_platform_rejected(self):
        a = self.fixture(); b = replace(a, hardware_id='different')
        with self.assertRaisesRegex(ValueError,'hardware'):p.compare_measured_verified_service(a,b)

    def test_incomplete_receipt_rejected(self):
        a = self.fixture()
        for change in ({'calibration_receipt':''},{'implementation_sha':''},
                       {'error_correction_proof_receipt':''},{'verified_outputs':0},
                       {'measured_joules':Decimal('NaN')},
                       {'measured_duration_s':Decimal(0)}):
            with self.assertRaises(ValueError): replace(a,**change).validate()

    def test_water_not_derived_from_operations(self):
        with self.assertRaisesRegex(ValueError,'measurement missing'):
            p.measured_water_per_it_kwh(None,Decimal(10))
        with self.assertRaisesRegex(ValueError,'measurement missing'):
            p.measured_water_per_it_kwh(Decimal(2),None)
        self.assertEqual(p.measured_water_per_it_kwh(Decimal(120),Decimal(60)),Decimal(2))

    def test_site_heat_not_subtracted_as_electric(self):
        # Equal electrical service energy does NOT become zero because
        # a heat customer can use heat: these remain distinct quantities.
        a = self.fixture()
        b = replace(a,recovered_heat_joules=Decimal(60))
        self.assertEqual(a.joules_per_verified_output(),b.joules_per_verified_output())

    def test_existing_original_heat_dispatch_exact(self):
        d = p.use_existing_thermal_dispatch(10000, 1.25, 2, 8.4)
        self.assertAlmostEqual(d.recovered_source_mw,8)
        self.assertAlmostEqual(d.hp_electric_mw,2.4)
        self.assertAlmostEqual(d.exported_heat_mw,10.4)
        self.assertAlmostEqual(d.rejected_mw,4.5)

    def test_heat_demand_dependent_existing_dispatch(self):
        d = p.use_existing_thermal_dispatch(10000, 1.25, 0, 0)
        self.assertAlmostEqual(d.exported_heat_mw,0)
        self.assertAlmostEqual(d.rejected_mw,12.5)

if __name__ == '__main__': unittest.main()
