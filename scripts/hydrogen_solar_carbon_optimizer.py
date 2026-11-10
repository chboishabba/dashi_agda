#!/usr/bin/env python3
"""Ideal solar→water H2→captured CO2→methane resource optimisation.

User-directed DASHI integration; ChatGPT-authored numerical calculator
(2026-11-10). Chemistry: classical Sabatier and electrolysis.
NIST standard-state HHVs, DASHI attributed SI/Atomic369 ownership retained.
Heat/electric reversible split: RSC 2022 DOI 10.1039/D2MA00185C.
NASA Sabatier and IEA AMF Task 64 are historical/process prior art.

Scenarios are theoretical allocations only. Carbon capture, heat recovery,
solar area/duty, product selectivity and fossil displacement remain external.
"""
from __future__ import annotations
from dataclasses import dataclass,asdict
from math import isfinite
import json
import argparse
import unittest

M_CO2_KG_PER_MOL=0.044009
M_H2_KG_PER_MOL=0.002016
M_H2O_KG_PER_MOL=0.018015
M_CH4_KG_PER_MOL=0.016043
H2_HHV_KJ_PER_MOL=285.830
CH4_HHV_KJ_PER_MOL=890.350
H2_REVERSIBLE_ELECTRIC_KJ_PER_MOL=237.13
H2_REVERSIBLE_HEAT_KJ_PER_MOL=H2_HHV_KJ_PER_MOL-H2_REVERSIBLE_ELECTRIC_KJ_PER_MOL
METHANATION_HEAT_CONDENSED_KJ_PER_CH4=4*H2_HHV_KJ_PER_MOL-CH4_HHV_KJ_PER_MOL


def pv_area_m2_for_energy(annual_electric_kwh:float,
                          annual_irradiance_kwh_m2:float,
                          solar_module_system_efficiency:float)->float:
    """Annual aperture area. Irradiance, performance and site are supplied,
    never inferred from the phrase 'put solar around the power plant'."""
    if annual_electric_kwh < 0 or annual_irradiance_kwh_m2 <= 0:
        raise ValueError('invalid solar resource/annual demand')
    if not 0 < solar_module_system_efficiency <= 1:
        raise ValueError('PV system efficiency must be in (0,1]')
    return annual_electric_kwh/(annual_irradiance_kwh_m2*
                               solar_module_system_efficiency)

def compare_direct_h2_vs_methane(engine_efficiency:float=0.4)->dict:
    """Same efficiency and 4 H2 feed: methanation loses useful fuel HHV.
    Applicability/storage/transport/emissions are NOT assumed equal."""
    if not 0 < engine_efficiency <= 1:
        raise ValueError('invalid assumed engine efficiency')
    return {
      'direct_h2_chemical_kwh_per_4mol':4*H2_HHV_KJ_PER_MOL/3600,
      'synthetic_methane_chemical_kwh_per_4mol':CH4_HHV_KJ_PER_MOL/3600,
      'direct_h2_work_kwh_assumed_same_eta':
           4*H2_HHV_KJ_PER_MOL/3600*engine_efficiency,
      'methane_work_kwh_assumed_same_eta':
           CH4_HHV_KJ_PER_MOL/3600*engine_efficiency,
      'methanation_condensed_reference_heat_kwh':
           METHANATION_HEAT_CONDENSED_KJ_PER_CH4/3600,
      'storage_and_fuel_compatibility_not_compared':True
    }

@dataclass(frozen=True)
class Inputs:
    co2_available_kg:float=1000.
    capture_fraction:float=1.
    solar_electric_kwh:float=10000.
    water_available_kg:float=10000.
    electrolyser_hhv_efficiency:float=1.
    methane_conversion:float=1.
    carbon_capture_kwh_per_mol:float=0.
    methanation_aux_kwh_per_mol:float=0.
    compatible_reaction_heat_fraction:float=0.
    thermal_integration:bool=False

def calculate(s:Inputs)->dict:
    d=asdict(s)
    for key,v in d.items():
        if isinstance(v,bool):continue
        if not isfinite(v) or v<0:raise ValueError(f'negative/nonfinite {key}')
    for k in ('capture_fraction','methane_conversion','electrolyser_hhv_efficiency',
              'compatible_reaction_heat_fraction'):
        if not 0 <= d[k] <= 1: raise ValueError(f'fraction out of range: {k}')
    if s.electrolyser_hhv_efficiency==0:
        raise ValueError('electrolyser efficiency must be positive')
    if s.methane_conversion==0:
        return {'methane_mol':0.,'reason':'zero methane yield'}
    # Product yield is defined per captured CO2. Unconverted CO2 is assumed
    # vented; capture electricity is paid on ALL captured feed.
    captured=s.co2_available_kg*s.capture_fraction/M_CO2_KG_PER_MOL
    carbon_product_limit=captured*s.methane_conversion
    heat_reusable_kj_per_product=min(
        4*H2_REVERSIBLE_HEAT_KJ_PER_MOL,
        s.compatible_reaction_heat_fraction*METHANATION_HEAT_CONDENSED_KJ_PER_CH4
    ) if s.thermal_integration else 0.
    # At eta=1, thermal integration can replace part of the nominal
    # thermoneutral electricity with source-qualified external reaction heat.
    # For eta <1, additional stack inefficiency remains electric.
    h2_electric_kj_per_product=(
        4*H2_HHV_KJ_PER_MOL/s.electrolyser_hhv_efficiency
        -heat_reusable_kj_per_product
    )
    # One mole of CH4 needs 1 mole converted CO2, 4 H2 and 4 H2O fed to
    # electrolysis, of which 2 H2O can be returned by methanation.
    # To honour captured-but-unconverted feed, capture burden/product=1/y.
    capture_kwh_per_product=s.carbon_capture_kwh_per_mol/s.methane_conversion
    electric_per_mol=h2_electric_kj_per_product/3600+capture_kwh_per_product+s.methanation_aux_kwh_per_mol
    if electric_per_mol<=0:raise ValueError('invalid energy cost')
    solar_limit=s.solar_electric_kwh/electric_per_mol
    water_limit=s.water_available_kg/(4*M_H2O_KG_PER_MOL)
    n=min(carbon_product_limit,solar_limit,water_limit)
    # Water feed is gross; recirculating methanation water gives net 2 H2O.
    return {
        'methane_mol':n,
        'methane_kg':n*M_CH4_KG_PER_MOL,
        'hydrogen_kg':n*4*M_H2_KG_PER_MOL,
        'co2_converted_kg':n*M_CO2_KG_PER_MOL,
        'gross_water_feed_kg':n*4*M_H2O_KG_PER_MOL,
        'process_water_recovered_kg':n*2*M_H2O_KG_PER_MOL,
        'net_water_consumed_kg':n*2*M_H2O_KG_PER_MOL,
        'oxygen_kg':n*2*0.031998,
        'methane_hhv_kwh':n*CH4_HHV_KJ_PER_MOL/3600,
        'solar_electricity_used_kwh':n*electric_per_mol,
        'reaction_heat_reusable_kwh':n*heat_reusable_kj_per_product/3600,
        'reaction_heat_thermochemical_kwh':n*METHANATION_HEAT_CONDENSED_KJ_PER_CH4/3600,
        'electric_kwh_per_mol_product':electric_per_mol,
        'limiting_resource':min(('co2',carbon_product_limit),('solar',solar_limit),
                                ('gross_water',water_limit),key=lambda t:t[1])[0],
        'output_electricity_kwh_at_40pct_generator':n*CH4_HHV_KJ_PER_MOL/3600*.4,
        'comparison_scope':'Captured atmospheric CO2 vs recycled fossil exhaust have different lifecycle claims.',
        'source_uncertainty':'No physical yield, heat integration or calibration certified.'
    }

class Checks(unittest.TestCase):
    def test_methane_chemistry(self):
        self.assertAlmostEqual(4*H2_HHV_KJ_PER_MOL,
            CH4_HHV_KJ_PER_MOL+METHANATION_HEAT_CONDENSED_KJ_PER_CH4)
    def test_one_kg_co2_ideal(self):
        x=calculate(Inputs(co2_available_kg=1,solar_electric_kwh=100,
                           water_available_kg=100))
        self.assertAlmostEqual(x['methane_kg'],M_CH4_KG_PER_MOL/M_CO2_KG_PER_MOL)
        self.assertAlmostEqual(x['net_water_consumed_kg'],
                               2*M_H2O_KG_PER_MOL/M_CO2_KG_PER_MOL)
        self.assertAlmostEqual(x['solar_electricity_used_kwh'],7.216,places=2)
    def test_solar_limited(self):
        x=calculate(Inputs(solar_electric_kwh=1))
        self.assertEqual(x['limiting_resource'],'solar')
        self.assertAlmostEqual(x['solar_electricity_used_kwh'],1)
    def test_co2_limited(self):
        x=calculate(Inputs(co2_available_kg=0.1))
        self.assertEqual(x['limiting_resource'],'co2')
    def test_water_limited(self):
        x=calculate(Inputs(water_available_kg=.1))
        self.assertEqual(x['limiting_resource'],'gross_water')
    def test_efficiency_monotonicity(self):
        a=calculate(Inputs(solar_electric_kwh=1,electrolyser_hhv_efficiency=1))
        b=calculate(Inputs(solar_electric_kwh=1,electrolyser_hhv_efficiency=.7))
        self.assertGreater(a['methane_mol'],b['methane_mol'])
    def test_capture_penalty(self):
        a=calculate(Inputs(solar_electric_kwh=1,methane_conversion=.5))
        b=calculate(Inputs(solar_electric_kwh=1,methane_conversion=.5,
                           carbon_capture_kwh_per_mol=.1))
        self.assertGreater(a['methane_mol'],b['methane_mol'])
    def test_heat_recovery_requires_explicit_opt_in(self):
        a=calculate(Inputs(solar_electric_kwh=1,thermal_integration=False,
                           compatible_reaction_heat_fraction=1))
        b=calculate(Inputs(solar_electric_kwh=1,thermal_integration=True,
                           compatible_reaction_heat_fraction=1))
        self.assertGreater(b['methane_mol'],a['methane_mol'])
        self.assertLessEqual(b['reaction_heat_reusable_kwh'],
                             b['reaction_heat_thermochemical_kwh'])
    def test_water_net_is_half_gross(self):
        x=calculate(Inputs(solar_electric_kwh=1))
        self.assertAlmostEqual(x['gross_water_feed_kg'],
                               2*x['net_water_consumed_kg'])
    def test_no_free_energy_without_external_supply(self):
        x=calculate(Inputs(solar_electric_kwh=0))
        self.assertEqual(x['methane_mol'],0.)
    def test_annual_pv_area_formula(self):
        self.assertAlmostEqual(pv_area_m2_for_energy(7.216453*1e9,1500,.2),
                               24054843.33,delta=500)
    def test_direct_h2_vs_methane_same_engine(self):
        d=compare_direct_h2_vs_methane(.4)
        self.assertGreater(d['direct_h2_work_kwh_assumed_same_eta'],
                           d['methane_work_kwh_assumed_same_eta'])
    def test_inadmissible_inputs_fail(self):
        with self.assertRaises(ValueError):
            calculate(Inputs(electrolyser_hhv_efficiency=1.5))

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--self-test',action='store_true')
    p.add_argument('--co2-kg',type=float,default=1000)
    p.add_argument('--solar-kwh',type=float,default=10000)
    p.add_argument('--gross-water-kg',type=float,default=10000)
    p.add_argument('--eta',type=float,default=1)
    p.add_argument('--heat-reuse',type=float,default=0)
    args=p.parse_args()
    if args.self_test:
        unittest.main(argv=['hydrogen_solar_carbon_optimizer.py'],verbosity=2)
    else:
        print(json.dumps(calculate(Inputs(
            co2_available_kg=args.co2_kg,solar_electric_kwh=args.solar_kwh,
            water_available_kg=args.gross_water_kg,
            electrolyser_hhv_efficiency=args.eta,
            compatible_reaction_heat_fraction=args.heat_reuse,
            thermal_integration=args.heat_reuse>0)),indent=2))
