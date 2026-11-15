#!/usr/bin/env python3
"""Synthetic data-centre heat dispatch; conservation-checked, NOT field-calibrated."""
from dataclasses import dataclass
from math import isclose

HOURS_YEAR = 8760

@dataclass(frozen=True)
class Parameters:
    it_mw: float = 10.0
    pue: float = 1.25
    capture_fraction_it: float = 0.80
    direct_capacity_mw: float = 2.0
    heat_pump_cop: float = 3.5
    source_c: float = 35.0
    sink_c: float = 75.0

    @property
    def carnot_cop(self):
        return (self.sink_c + 273.15) / (self.sink_c - self.source_c)

    def validate(self):
        assert self.it_mw >= 0 and self.pue >= 1.0
        assert 0 <= self.capture_fraction_it <= 1
        assert self.direct_capacity_mw >= 0 and self.heat_pump_cop > 1
        assert self.sink_c > self.source_c > -273.15
        assert self.heat_pump_cop <= self.carnot_cop + 1e-9

@dataclass(frozen=True)
class ThermalDispatch:
    direct_mw: float
    hp_source_mw: float
    hp_electric_mw: float
    hp_hot_mw: float
    rejected_mw: float

    @property
    def exported_heat_mw(self):
        return self.direct_mw + self.hp_hot_mw

    @property
    def recovered_source_mw(self):
        return self.direct_mw + self.hp_source_mw

def dispatch(params, demand_direct_mw, demand_high_mw):
    """Direct-first demonstration, not profit-optimal dispatch."""
    params.validate()
    if min(demand_direct_mw, demand_high_mw) < 0:
        raise ValueError("negative heat demand")
    captured = params.it_mw * params.capture_fraction_it
    direct = min(demand_direct_mw, params.direct_capacity_mw, captured)
    hp_source = min(captured-direct,
                    demand_high_mw * (params.heat_pump_cop-1)/params.heat_pump_cop)
    hp_electric = hp_source / (params.heat_pump_cop-1)
    hp_hot = hp_source + hp_electric
    site_electric = params.it_mw * params.pue
    rejected = site_electric - direct - hp_source
    assert rejected >= -1e-10
    assert isclose(site_electric+hp_electric, direct+hp_hot+rejected, abs_tol=1e-9)
    assert hp_hot <= demand_high_mw+1e-9
    return ThermalDispatch(direct,hp_source,hp_electric,hp_hot,rejected)

def year(rows):
    rows = list(rows)
    assert len(rows)==HOURS_YEAR
    return {k:sum(getattr(d,k) for d in rows)/1000 for k in (
        "direct_mw","hp_source_mw","hp_electric_mw","hp_hot_mw","rejected_mw",
        "exported_heat_mw","recovered_source_mw")}

def carbon_break_even_grid_t_per_mwh(d, gas_factor=0.2, gas_boiler_efficiency=0.9):
    """Only comparison to an assumed displaced gas boiler; excludes other auxiliaries."""
    if d.hp_electric_mw==0:
        return float("inf") if d.exported_heat_mw>0 else 0.0
    return d.exported_heat_mw/gas_boiler_efficiency*gas_factor/d.hp_electric_mw

def absorption_cooling(source_heat_mw, thermal_cop=0.35):
    """Illustrative 50C multistage absorption, not sourced plant-performance COP."""
    assert source_heat_mw >=0 and thermal_cop >=0
    chilling_mw=source_heat_mw*thermal_cop
    return dict(source_heat_mw=source_heat_mw,chilling_mw=chilling_mw,
                heat_rejected_mw=source_heat_mw+chilling_mw)

def exergy_fraction(source_c,environment_c):
    assert source_c>environment_c>-273.15
    return 1-(environment_c+273.15)/(source_c+273.15)

def example_scenarios():
    p=Parameters()
    ideal=dispatch(p,2.0,8.4)
    assert all(isclose(x,y) for x,y in (
        (ideal.hp_source_mw,6.0),(ideal.hp_electric_mw,2.4),
        (ideal.hp_hot_mw,8.4),(ideal.exported_heat_mw,10.4),
        (ideal.rejected_mw,4.5)))
    always=year(dispatch(p,2,8.4) for _ in range(HOURS_YEAR))
    day_shift=year(dispatch(p,1,6) if h%24 in range(8,18)
                   else dispatch(p,0,0) for h in range(HOURS_YEAR))
    seasonal=year(dispatch(p,0,3) if d<100 and 8<=h<16
                   else dispatch(p,0,0) for d in range(365) for h in range(24))
    print("Hypothetical: 10MW IT, PUE 1.25, 80% capture, HP COP 3.5")
    print("Carnot upper bound 35C -> 75C:",round(p.carnot_cop,3))
    for title,v in (("24/7 matched",always),("10h/day commercial",day_shift),
                    ("100d 8h/day winter",seasonal)):
        print(title, "heat_export_GWh",round(v["exported_heat_mw"],3),
              "extra_HP_electric_GWh",round(v["hp_electric_mw"],3),
              "captured_source_GWh",round(v["recovered_source_mw"],3))
    print("Illustrative gas-boiler carbon break-even grid tCO2/MWh:",
          round(carbon_break_even_grid_t_per_mwh(ideal),3))
    print("Illustrative 50C absorption:",absorption_cooling(6))
    print("Heat exergy vs 30C ambient: 35C:",round(exergy_fraction(35,30),4),
          "45C:",round(exergy_fraction(45,30),4))

if __name__=="__main__":
    example_scenarios()
