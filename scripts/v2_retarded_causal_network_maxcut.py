#!/usr/bin/env python3
"""Finite-speed signal-front and causal routing controls for V2 motor models.

SOURCE: Reuses SmithFilsingerTimeIndexedTransferExact.RetardedFlight and
scripts/check_smith_filsinger_causal_nonlinear_maxcut.py as independent donors.
This is a *signal network* test, NOT a Maxwell field or V2 measurement.

Causality: no information-bearing field front can arrive sooner than d/c.
The local machine's lumped mutual-inductance coupling is a quasistatic limit,
not a proof of instantaneous distant state propagation. Material, cable,
controller and mechanical response may be slower than the vacuum bound.

Discretisation: a piecewise constant source is propagated via integer
ceil(tau/dt) samples, which is conservative by <dt per hop. This must NOT
be used directly as a delay in the coarse rotor-state RK4 integrator, where
one model timestep is much larger than the actual nanosecond flight time.
"""
from __future__ import annotations
from dataclasses import asdict, dataclass
import json
import math
import numpy as np

C_M_PER_S = 299_792_458.0


@dataclass(frozen=True)
class CausalLink:
    name: str
    length_m: float
    front_speed_m_s: float
    amplitude_transmission: float = 1.0

    def validate(self) -> None:
        if not (math.isfinite(self.length_m) and self.length_m >= 0):
            raise ValueError('link length must be nonnegative and finite')
        if not (math.isfinite(self.front_speed_m_s)
                and 0 < self.front_speed_m_s <= C_M_PER_S):
            raise ValueError('information-front velocity cannot exceed c')
        if not (math.isfinite(self.amplitude_transmission)
                and 0 <= self.amplitude_transmission <= 1):
            raise ValueError('passive single-link transmission must be within [0,1]')

    @property
    def delay_s(self) -> float:
        self.validate()
        return self.length_m / self.front_speed_m_s

    @property
    def vacuum_lower_bound_s(self) -> float:
        self.validate()
        return self.length_m / C_M_PER_S

    def flight_ticks(self, dt_s: float) -> int:
        if not (math.isfinite(dt_s) and dt_s > 0):
            raise ValueError('sample interval must be positive finite')
        flight = self.delay_s
        if flight == 0.0:
            return 0
        # Conservative sampled step-front: no arrival before the continuous
        # flight time even if tau<dt. Guard unavoidable round-off near ticks.
        ticks = math.ceil(flight / dt_s - 1e-12)
        return max(1, int(ticks))


def delayed_samples(samples, link: CausalLink, dt_s: float) -> np.ndarray:
    """Passive causal delayed path for a sampled zero-order-hold signal.

    This models a single input-to-output causal edge, not instantaneous KCL
    and not a claim of source power equal to squared signal amplitude.
    """
    a = np.asarray(samples, dtype=float)
    if a.ndim != 1 or not np.all(np.isfinite(a)):
        raise ValueError('finite one-dimensional signal required')
    steps = link.flight_ticks(dt_s)
    out = np.zeros_like(a)
    if steps < a.size:
        if steps:
            out[steps:] = link.amplitude_transmission * a[:-steps]
        else:
            out[:] = link.amplitude_transmission * a
    return out


def route_signal(samples, links: list[CausalLink], dt_s: float) -> np.ndarray:
    if not links:
        raise ValueError('a spatial path needs at least one declared link')
    out = np.asarray(samples, dtype=float)
    for link in links:
        out = delayed_samples(out, link, dt_s)
    return out


def route_receipt(links: list[CausalLink], dt_s: float) -> dict:
    if not links:
        raise ValueError('route must be nonempty')
    if not (math.isfinite(dt_s) and dt_s > 0):
        raise ValueError('positive time resolution required')
    distance = sum(edge.length_m for edge in links)
    tau = sum(edge.delay_s for edge in links)
    sampled_ticks = sum(edge.flight_ticks(dt_s) for edge in links)
    sampled_tau = sampled_ticks * dt_s
    lightcone_tau = distance / C_M_PER_S
    assert sampled_tau + 1e-15 >= tau
    assert tau + 1e-15 >= lightcone_tau
    return dict(links=[asdict(e) for e in links],path_m=distance,
                fastest_vacuum_arrival_s=lightcone_tau,
                continuous_front_delay_s=tau,
                conservative_sampled_arrival_s=sampled_tau,
                discrete_ticks=sampled_ticks,
                overshoot_s=sampled_tau-tau,
                bounded_by_total_per_hop_grid_error_s=len(links)*dt_s,
                finite_speed_pass=True,
                source='conditional specified link geometry, not original V2 wiring')


def quasistatic_scale(link: CausalLink, signal_hz: float) -> dict:
    if not (math.isfinite(signal_hz) and signal_hz >= 0):
        raise ValueError('nonnegative finite frequency required')
    # |omega*tau| small is a frequency-domain *indicator*, not a rigorous
    # electromagnetic model-reduction error bound or controller guarantee.
    return dict(frequency_hz=signal_hz,front_delay_s=link.delay_s,
                omega_tau_rad=2*math.pi*signal_hz*link.delay_s,
                wavelength_in_link_m=(link.front_speed_m_s/signal_hz)
                    if signal_hz else None,
                interpretation='scale diagnostic only; requires separate field-error theorem')


def run() -> dict:
    rpm = 2354.0
    shaft_period_s = 60/rpm
    pwm_hz = 20_000.0  # existing synthetic coupled-generator parameter
    # THESE distances/speeds are illustrative, not measured V2 cables.
    cable = CausalLink('illustrative 0.5 m cable',0.5,0.7*C_M_PER_S,0.9)
    round_trip=[cable,cable]
    fine_dt_s=1e-9
    n=40
    impulse=np.zeros(n); impulse[0]=1.0
    obs=route_signal(impulse,round_trip,fine_dt_s)
    receipt=route_receipt(round_trip,fine_dt_s)
    assert np.all(obs[:receipt['discrete_ticks']]==0)
    assert abs(obs[receipt['discrete_ticks']]-0.9**2)<1e-14
    scales=quasistatic_scale(cable,pwm_hz)
    return dict(scope='source-independent finite-front routing; no measured V2 geometry',
                donor='Smith/Filsinger discrete RetardedFlight, time-indexed transfer and Maxwell source boundaries',
                c_m_per_s=C_M_PER_S,
                example_half_meter_cable=asdict(cable),
                example_round_trip=receipt,
                shaft_period_s=shaft_period_s,
                pwm_period_s=1/pwm_hz,
                existing_180_steps_per_rev_step_s=shaft_period_s/180,
                pwm_phase_scale=scales,
                invalid_inference='a lumped mutual L has no literal superluminal field; it is an approximation requiring causality-error control',
                remaining_gates=['v2SpatialCausalRetardedMagneticFieldWeld',
                  'v2DistributedLineMaxwellPassivityAndWavefrontBound',
                  'v2LumpedQuasistaticErrorAndControllerLatencyBound',
                  'v2ActualCableGeometryMaterialAndProbeDelayReceipt'])


if __name__=='__main__':
    print(json.dumps(run(),indent=2))
