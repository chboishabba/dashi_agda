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


def dispatch_choice(solar_kwh: float, co2_kg: float, water_kg: float,
                    directly_usable_solar_fraction: float = 1.0,
                    methane_generator_efficiency: float = 0.4,
                    stored_electricity_value_multiplier: float = 1.0,
                    electrolyser_hhv_efficiency: float = 1.0,
                    capture_fraction: float = 1.0,
                    conversion_fraction: float = 1.0,
                    carbon_capture_kwh_per_mol: float = 0.0,
                    reactor_aux_kwh_per_mol: float = 0.0) -> dict:
    """Solve the two-option LINEAR energy-service allocation exactly at corners.

    PV may go directly to currently deliverable demand, or be converted into
    methane for future generating service. A fixed value multiplier may
    approximate the value of dispatchability, but it is NOT a real tariff.
    All captured CO2 incurs capture work even if synthesis yield < 1.
    Gross-water intake and CO2 are independent constraints.
    No capture/synthesis heat reuse is assumed in this branch.
    """
    from math import isfinite
    values=(solar_kwh,co2_kg,water_kg,directly_usable_solar_fraction,
            methane_generator_efficiency,stored_electricity_value_multiplier,
            electrolyser_hhv_efficiency,capture_fraction,conversion_fraction,
            carbon_capture_kwh_per_mol,reactor_aux_kwh_per_mol)
    if any(not isfinite(v) or v < 0 for v in values):
        raise ValueError('negative/nonfinite dispatch parameters')
    if any(v > 1 for v in (directly_usable_solar_fraction,
                          methane_generator_efficiency,capture_fraction,
                          conversion_fraction,electrolyser_hhv_efficiency)):
        raise ValueError('fractions may not exceed one')
    if electrolyser_hhv_efficiency <= 0:
        raise ValueError('electrolyser efficiency must be positive')
    captured=co2_kg/M_CO2_KG_PER_MOL*capture_fraction
    product_capacity=captured*conversion_fraction
    h2_electric_kwh_per_product=4*H2_HHV_KJ_PER_MOL/3600/electrolyser_hhv_efficiency
    if conversion_fraction == 0:
        methane_mol=0.
        energy_cost=0.
        carbon_cap=0.
        marginal_methane=0.
    else:
        energy_cost=(h2_electric_kwh_per_product
            +carbon_capture_kwh_per_mol/conversion_fraction
            +reactor_aux_kwh_per_mol)
        carbon_cap=min(product_capacity,water_kg/(4*M_H2O_KG_PER_MOL))
        marginal_methane=(
            CH4_HHV_KJ_PER_MOL/3600*methane_generator_efficiency*
            stored_electricity_value_multiplier/energy_cost
        )
        # Corner solution for a linear program with solar, carbon, and
        # water bounds. All fuel is product-assayed and deliverable only
        # as an ASSUMPTION, not physical evidence.
        methane_mol=(min(carbon_cap,solar_kwh/energy_cost)
                     if marginal_methane > directly_usable_solar_fraction else 0.)
    solar_to_methane=methane_mol*energy_cost
    methane_service=(methane_mol*CH4_HHV_KJ_PER_MOL/3600*
                     methane_generator_efficiency*stored_electricity_value_multiplier)
    direct_service=(solar_kwh-solar_to_methane)*directly_usable_solar_fraction
    return {
        'decision':('prioritise_methane' if methane_mol>0 else 'prioritise_direct_pv'),
        'methane_mol':methane_mol,
        'solar_to_methane_kwh':solar_to_methane,
        'solar_to_direct_kwh':solar_kwh-solar_to_methane,
        'valued_methane_service_units':methane_service,
        'valued_direct_pv_service_units':direct_service,
        'total_valued_service_units':methane_service+direct_service,
        'methane_service_per_solar_kwh':marginal_methane,
        'direct_service_per_solar_kwh':directly_usable_solar_fraction,
        'carbon_limited_moles':carbon_cap,
        'note':'Ideal linear schedule; no ramping, equipment cost, storage loss or physical data.'
    }


def steady_state_carbon_inventory(carbon_duty_kg_per_period:float,
                                  effective_recovery_fraction:float,
                                  periods:int)->dict:
    """Fixed carbon consumption EACH period, NOT attrition of one batch.

    First period is entirely virgin fossil carbon. In each later period,
    fraction q of the immediately preceding output is recovered, and
    (1-q) is replaced to keep the same fuel output. Water/PV energy inputs
    for converting q*C CO2 into fuel remain payable each period.
    """
    from math import isfinite
    if (not isfinite(carbon_duty_kg_per_period) or
        carbon_duty_kg_per_period < 0 or
        not isfinite(effective_recovery_fraction) or
        not 0<=effective_recovery_fraction<=1 or
        type(periods) is not int or periods < 1):
        raise ValueError('invalid fixed-demand carbon-cycle inputs')
    c=carbon_duty_kg_per_period
    q=effective_recovery_fraction
    virgin=c+(periods-1)*(1-q)*c
    return {
        'total_carbon_fuel_duty_kg':periods*c,
        'virgin_carbon_kg':virgin,
        'reused_carbon_kg':(periods-1)*q*c,
        'virgin_baseline_kg':periods*c,
        'avoided_virgin_kg':(periods-1)*q*c,
        'steady_period_virgin_makeup_kg':(1-q)*c,
        'repeated_recycled_carbon_not_atmospheric_removal':True,
        'external_solar_energy_per_recovered_batch_still_required':True
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

    def test_fixed_output_recycling_does_not_assume_one_finite_batch(self):
        x=steady_state_carbon_inventory(100,0.9,10)
        self.assertAlmostEqual(x['virgin_carbon_kg'],190)
        self.assertAlmostEqual(x['avoided_virgin_kg'],810)
        self.assertAlmostEqual(x['virgin_carbon_kg']+x['reused_carbon_kg'],1000)
    def test_direct_pv_dominates_simultaneous_same_value(self):
        x=dispatch_choice(100,100,100,directly_usable_solar_fraction=1)
        self.assertEqual(x['methane_mol'],0)
        self.assertAlmostEqual(x['solar_to_direct_kwh'],100)
    def test_storage_wins_if_direct_pv_cannot_serve_demand(self):
        x=dispatch_choice(100,100,100,directly_usable_solar_fraction=0.2)
        self.assertGreater(x['methane_mol'],0)
        self.assertGreater(x['methane_service_per_solar_kwh'],
                           x['direct_service_per_solar_kwh'])
    def test_methane_cap_co2_and_water(self):
        x=dispatch_choice(1e6,.044009,.07206,directly_usable_solar_fraction=0)
        self.assertAlmostEqual(x['methane_mol'],1)
    def test_zero_co2_no_methane(self):
        x=dispatch_choice(100,0,100,directly_usable_solar_fraction=0)
        self.assertEqual(x['methane_mol'],0)
    def test_capture_work_reduces_served_methane(self):
        a=dispatch_choice(10,100,100,directly_usable_solar_fraction=0,
                          carbon_capture_kwh_per_mol=0)
        b=dispatch_choice(10,100,100,directly_usable_solar_fraction=0,
                          carbon_capture_kwh_per_mol=.1)
        self.assertGreater(a['methane_mol'],b['methane_mol'])
    def test_dispatch_rejects_unphysical_fraction(self):
        with self.assertRaises(ValueError):
            dispatch_choice(1,1,1,methane_generator_efficiency=1.1)

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
