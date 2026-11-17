#!/usr/bin/env python3
"""F13-F16 source-first maximum cut; *no* original hardware claim.

F13: Crowley (2011) isolated elevated sphere, fair-weather DC current.
F14/15: signed terminal work, uncertainty and source observability.
F16: cloud-causality counterworld: association != controlled response.

Source: J. M. Crowley, The Fair-Weather Atmosphere as a Power Source,
Proc. ESA Annual Meeting on Electrostatics 2011, Eq. 28-37.
2026 Borok mean J (Anisimov et al.): DOI 10.1016/j.asr.2026.01.090.
This does not predict a ground-level plate or Filsinger's Earth wires.
"""
from __future__ import annotations
from dataclasses import dataclass
import json
from math import pi, isfinite

BOROK_MEAN_J = 2.36e-12


def _pos(*values):
    if not all(isfinite(x) and x > 0 for x in values):
        raise ValueError('positive finite values required')


@dataclass(frozen=True)
class CrowleyIsolatedSphere:
    height_m: float
    diameter_m: float
    atmospheric_potential_V: float
    local_E_V_m: float
    current_density_A_m2: float = BOROK_MEAN_J

    def __post_init__(self):
        _pos(self.height_m,self.diameter_m,self.atmospheric_potential_V,
             self.local_E_V_m,self.current_density_A_m2)
        if self.height_m < 10*self.diameter_m:
            raise ValueError('isolated sphere needs height >> diameter; h >=10d screening only')

    @property
    def conductivity_S_m(self):
        return self.current_density_A_m2/self.local_E_V_m

    @property
    def voc_V(self):
        return self.atmospheric_potential_V

    @property
    def isc_A(self):
        return 2*pi*self.diameter_m*self.conductivity_S_m*self.voc_V

    @property
    def source_R_ohm(self):
        return 1/(2*pi*self.diameter_m*self.conductivity_S_m)

    @property
    def matched_W(self):
        return self.voc_V*self.isc_A/4

    @property
    def effective_collection_area_m2(self):
        return self.isc_A/self.current_density_A_m2

    @property
    def geometric_projected_area_m2(self):
        # The actual physical projected disc of a sphere of DIAMETER d.
        return pi*self.diameter_m**2/4

    @property
    def enhancement_over_projected_area(self):
        return self.effective_collection_area_m2/self.geometric_projected_area_m2

    def load_W(self, load_resistance_ohm: float):
        _pos(load_resistance_ohm)
        r=self.source_R_ohm
        return self.voc_V**2*load_resistance_ohm/(r+load_resistance_ohm)**2

    def report(self):
        return dict(height_m=self.height_m,diameter_m=self.diameter_m,
           potential_V=self.voc_V,field_V_m=self.local_E_V_m,
           conductivity_S_m=self.conductivity_S_m,
           short_circuit_A=self.isc_A,source_R_ohm=self.source_R_ohm,
           matched_W=self.matched_W,effective_area_m2=self.effective_collection_area_m2,
           projected_area_m2=self.geometric_projected_area_m2,
           collection_enhancement_over_projected=self.enhancement_over_projected_area,
           source='Crowley Eq.28-37; isolated elevated sphere, not a plate or soil pair')


def local_uniform_collector(height_m=2.,diameter_m=.1,E_V_m=100.,j_A_m2=BOROK_MEAN_J):
    _pos(height_m,diameter_m,E_V_m,j_A_m2)
    return CrowleyIsolatedSphere(height_m,diameter_m,E_V_m*height_m,E_V_m,j_A_m2)


def layered_phi(height_m,field_layers):
    """Potential difference from a specified piecewise-constant E(z).

    field_layers sequence of (upper_altitude_m, E_V_m), sorted with first top >0.
    Nothing here solves the field equations; it integrates an *assumed* profile.
    """
    _pos(height_m)
    prev=0.
    phi=0.
    if not field_layers:raise ValueError('missing profile')
    for top,e in field_layers:
        _pos(top,e)
        if top<=prev:raise ValueError('non-increasing layer boundaries')
        end=min(top,height_m)
        phi+=max(end-prev,0)*e
        if top>=height_m:return phi
        prev=top
    raise ValueError('profile does not cover height')


@dataclass(frozen=True)
class VIMeterSample:
    dt_s: float
    v_V: float
    i_A: float
    v_error_V: float = 0.
    i_error_A: float = 0.

    def __post_init__(self):
        if not all(isfinite(x) for x in (self.dt_s,self.v_V,self.i_A,self.v_error_V,self.i_error_A)):
            raise ValueError('nonfinite electrical sample')
        if self.dt_s<=0 or self.v_error_V<0 or self.i_error_A<0:
            raise ValueError('invalid sample duration/error')

    def energy_interval_J(self):
        """Conservative product interval, I positive INTO receiver.

        For AC, voltages/currents must be truly time-synchronous samples with
        relevant bandwidth: multiplying separately averaged RMS is invalid.
        """
        vs=(self.v_V-self.v_error_V,self.v_V+self.v_error_V)
        currents=(self.i_A-self.i_error_A,self.i_A+self.i_error_A)
        products=[a*b*self.dt_s for a in vs for b in currents]
        return min(products),max(products)


def total_port_interval(samples):
    if not samples:raise ValueError('no synchronous measurements')
    intervals=[s.energy_interval_J() for s in samples]
    return sum(x[0] for x in intervals),sum(x[1] for x in intervals)


def meter_gate(samples,source_state_restored=False,independent_source_identity=False):
    lo,hi=total_port_interval(samples)
    return dict(natural_work_lower_J=lo,natural_work_upper_J=hi,
       positive_signed_port_work_certified=lo>0,
       sustained_source_gate_admissible=bool(lo>0 and source_state_restored and independent_source_identity),
       warns='Source restoration/identity are external physical evidence, not derived from meter voltage/current')


def rank_observation_cut():
    """Without measuring ports, a single output balance has 3 free terms.

    Unknowns [W_natural,W_drive_and_control,W_losses,DeltaU] satisfy
    W_load=natural+drive-loss-DeltaU. Construct 3 indistinguishable worlds.
    """
    rows=[(0.,5.,1.,0.),(3.,2.,1.,0.),(0.,0.,0.,-4.)]
    def load(q):return q[0]+q[1]-q[2]-q[3]
    assert all(load(q)==4 for q in rows)
    return dict(observation='only useful load 4 J',linear_balance_rank=1,
        unidentified_degrees_of_freedom=3,
        donor_worlds=[dict(natural=q[0],driver=q[1],loss=q[2],stored_delta=q[3],load=load(q)) for q in rows],
        conclusion='same load can be driver, natural supply, or stored-energy depletion')


def causal_cloud_counterworld(ambient=1.,observed_rain=2.,u=1.,cloud_field_control_gain=.1):
    """Two structural worlds with same natural E/rain observation but different do(u).

    E = ambient + k*u, rain = a*ambient + b*E.
    Natural observations u=0: E=ambient, rain=2*ambient.
    World A a=2,b=0; World B a=0,b=2.
    Identical observational series for every ambient, different intervention.
    This is an identifiability counterexample, NOT a rain response estimate.
    """
    if not all(isfinite(x) for x in (ambient,observed_rain,u,cloud_field_control_gain)):
        raise ValueError('finite causal inputs required')
    if ambient==0:raise ValueError('nonzero ambient to define observed slope')
    r=observed_rain/ambient
    field_natural=ambient
    field_controlled=ambient+cloud_field_control_gain*u
    worlds=[dict(name='no field-to-rain effect',a=r,b=0),
            dict(name='field-mediated rain effect',a=0,b=r)]
    for w in worlds:
        w['observational_E']=field_natural
        w['observational_rain']=w['a']*ambient+w['b']*field_natural
        w['intervention_rain']=w['a']*ambient+w['b']*field_controlled
        w['causal_change']=w['intervention_rain']-w['observational_rain']
    assert worlds[0]['observational_rain']==worlds[1]['observational_rain']
    return dict(worlds=worlds,identification='correlation alone does not fix intervention gain',
                clouds_not_actuated_if_field_gain_zero=cloud_field_control_gain==0)


def summary():
    s=local_uniform_collector()
    i=s.report()
    i['matched_full_source_limit_W']=s.matched_W
    i['local_uniform_field_potential_assumption_V']=200.
    return dict(scope='F13-F16 conditional source access and falsification; no original source admission',
                spherical_collector=i,
                older_slabs_are_different='one-dimensional slab aperture does not describe spherical field focusing',
                geometry_warning='Crowley Eq32 uses pi*d^2 as a cross sectional area although d is defined as diameter: actual projected sphere area is pi*d^2/4. Short-circuit formula Eq28 and power Eq37 remain unchanged.',
                loaded_only_identifiability=rank_observation_cut(),
                cloud_nonidentifiability=causal_cloud_counterworld(),
                original_physical_gates=['S0','P1','P2','R1','R2','R3','D1','D2'])

if __name__=='__main__':print(json.dumps(summary(),indent=2))
