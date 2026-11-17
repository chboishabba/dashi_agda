#!/usr/bin/env python3
"""Conditional Earth/air source-access models, not fitted Filsinger hardware.

Reuses the fixed-source matching logic from check_smith_filsinger_shunt_source_port,
the existing global-circuit scale test, and the dispersive source-port ledger.
Do not identify the 7.8 kHz acoustic carrier with an electrical clock.
"""
from dataclasses import dataclass
from math import pi, sqrt, isfinite
import json

EPS0 = 8.8541878128e-12
C = 299_792_458.0
J_BOROK_MEAN = 2.36e-12
J_BOROK_MODE = 1.25e-12

def positive(*values):
    if not all(isfinite(v) and v > 0 for v in values):
        raise ValueError("finite positive parameters required")

@dataclass(frozen=True)
class DCColumn:
    voltage_V: float
    current_density_A_m2: float
    accessible_area_m2: float

    def __post_init__(self):
        positive(self.voltage_V, self.current_density_A_m2, self.accessible_area_m2)

    @property
    def short_circuit_A(self):
        return self.current_density_A_m2 * self.accessible_area_m2

    @property
    def conductance_S(self):
        return self.short_circuit_A / self.voltage_V

    @property
    def resistance_ohm(self):
        return 1 / self.conductance_S

    @property
    def matched_load_W(self):
        return self.voltage_V * self.short_circuit_A / 4

    def terminal_power_W(self, receiver_current_A):
        if not isfinite(receiver_current_A):
            raise ValueError("finite current required")
        return (self.voltage_V - self.resistance_ohm * receiver_current_A) * receiver_current_A

    def needed_area_m2(self, requested_load_W):
        positive(requested_load_W)
        return requested_load_W / (self.voltage_V * self.current_density_A_m2 / 4)

def vertical_near_surface_admittance(E_V_m, height_m, area_m2, j_A_m2, frequency_hz):
    """Uniform near-ground 1D G+i omega C. AC displacement is not natural work."""
    positive(E_V_m, height_m, area_m2, j_A_m2)
    if not isfinite(frequency_hz) or frequency_hz < 0:
        raise ValueError("nonnegative frequency required")
    sigma = j_A_m2 / E_V_m
    return complex(sigma*area_m2/height_m,
                   2*pi*frequency_hz*EPS0*area_m2/height_m)

def soil_pair_far_separated_resistance_ohm(resistivity_ohm_m, hemisphere_radius_m):
    """DC asymptotic: two hemispheres, separation much greater than radius."""
    positive(resistivity_ohm_m, hemisphere_radius_m)
    return resistivity_ohm_m / (pi*hemisphere_radius_m)

def required_soil_open_voltage_V(resistivity_ohm_m, hemisphere_radius_m, power_W):
    positive(power_W)
    return sqrt(4 * soil_pair_far_separated_resistance_ohm(
        resistivity_ohm_m, hemisphere_radius_m) * power_W)

def debye_admittance(frequency_hz, G_S, C_F, terms):
    """Passive Y(s)=G+s*C+sum(g*s*tau/(1+s*tau)), with s=i*omega."""
    if not all(isfinite(v) and v >= 0 for v in (frequency_hz,G_S,C_F)):
        raise ValueError("finite nonnegative frequency/G/C required")
    s = complex(0,2*pi*frequency_hz)
    y = G_S+s*C_F
    for g,tau in terms:
        positive(g,tau)
        y += g*s*tau/(1+s*tau)
    return y

def debye_port_energy_rate(voltage, voltage_dot, memory_states, G_S, C_F, terms):
    """Return (V*I, dU/dt, P_loss), with tau*x'=V-x.

    Exact passivity: V*I = d/dt[C*V^2/2+sum(g*tau*x^2/2)]
                            + G*V^2 + sum(g*(V-x)^2).
    For two terminals take V=Vs-Vreceiver. No extra environmental source
    is created by the field or the polarization memory.
    """
    if len(memory_states) != len(terms):
        raise ValueError("memory state/term mismatch")
    current = G_S*voltage+C_F*voltage_dot
    udot = C_F*voltage*voltage_dot
    loss = G_S*voltage*voltage
    for x,(g,tau) in zip(memory_states,terms):
        positive(g,tau)
        xdot = (voltage-x)/tau
        current += g*(voltage-x)
        udot += g*tau*x*xdot
        loss += g*(voltage-x)**2
    return current*voltage,udot,loss

def front_scale(frequency_hz, path_m):
    """omega*d/c diagnostic, not a full Maxwell error theorem."""
    if not all(isfinite(v) and v >= 0 for v in (frequency_hz,path_m)):
        raise ValueError("nonnegative finite frequency and length required")
    return 2*pi*frequency_hz*path_m/C

def scenario():
    full = DCColumn(250000,J_BOROK_MEAN,1)
    local = DCColumn(200,J_BOROK_MEAN,1)
    ratios = {}
    for f in (7.83,7800):
        y = vertical_near_surface_admittance(100,2,1,J_BOROK_MEAN,f)
        ratios[str(f)] = dict(G_S=y.real, susceptance_S=y.imag,
            reactive_to_conductive=y.imag/y.real,
            omega_H_over_c=front_scale(f,80000))
    return dict(
       scope="idealized DC source access and passive material, not Filsinger device",
       atmospheric_full_column=dict(Voc_V=full.voltage_V,
           G_per_m2_S=full.conductance_S,
           Rcol_per_m2_ohm=full.resistance_ohm,
           Pmatched_per_m2_W=full.matched_load_W,
           needed_area_0p4W_km2=full.needed_area_m2(.4)/1e6,
           needed_area_6p7W_km2=full.needed_area_m2(6.7)/1e6),
       near_ground_2m_100Vm=dict(Voc_V=local.voltage_V,
           Pmatched_per_m2_W=local.matched_load_W,
           needed_area_0p4W_km2=local.needed_area_m2(.4)/1e6,
           needed_area_6p7W_km2=local.needed_area_m2(6.7)/1e6),
       far_separated_ground_pair=dict(rho_ohm_m=100,hemisphere_radius_m=.1,
           approximate_Rpair_ohm=soil_pair_far_separated_resistance_ohm(100,.1),
           minimum_Voc_for_0p4W_V=required_soil_open_voltage_V(100,.1,.4),
           minimum_Voc_for_6p7W_V=required_soil_open_voltage_V(100,.1,6.7)),
       driven_air_reactive_conduction_ratios=ratios,
       original_gates="S0/P1/P2/R1/R2/R3/D1/D2 OPEN")

if __name__ == "__main__":
    print(json.dumps(scenario(),indent=2,sort_keys=True))
