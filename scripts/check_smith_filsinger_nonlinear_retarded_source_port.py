#!/usr/bin/env python3
"""Conditional F10/F13/F15 causal port and electron-continuity test bench.

No atmospheric intervention parameters, source measurements or actual Filsinger
hardware claim. Reuses #1521 constitutive/source and #1524 source-first
evidence categories without constructing evidence from model outputs.

Passive Foster branches are LTI; active external solar forcing is a separately
paid source. A delayed active feedback term is NOT guaranteed positive-real.
"""
from dataclasses import dataclass
import json
import math
import sympy as sp

E_CHARGE = 1.602176634e-19

def exact_identity_checks():
    s,g,w,alpha,gamma,omega=sp.symbols(
        "s g w alpha gamma omega", positive=True, real=True)
    jw=sp.I*omega
    y_debye=g*jw/(jw+w)
    y_lorentz=alpha*jw/(omega**2*-1+sp.I*gamma*omega+w**2)
    assert sp.simplify(sp.re(sp.expand_complex(y_debye)) -
        g*omega**2/(w**2+omega**2)) == 0
    assert sp.simplify(sp.re(sp.expand_complex(y_lorentz)) -
        alpha*gamma*omega**2/((w**2-omega**2)**2+gamma**2*omega**2)) == 0

    V,q,qd,C,gd,a,W,G0,G2=sp.symbols(
        "V q qd C gd a W G0 G2",real=True)
    # Debye state q' = w(V-q); i=g(V-q); storage g q²/(2w).
    qdot=w*(V-q)
    assert sp.expand(V*g*(V-q)-g*(V-q)**2-(g/w)*q*qdot)==0
    # Resonance q''+gamma*q'+w²q=V; i=alpha*q'.
    qddot=V-gamma*qd-w*w*q
    assert sp.expand(V*alpha*qd-alpha*gamma*qd**2 -
                     alpha*(qd*qddot+w*w*q*qd))==0
    # cubic nonlinear passive conductance: differential != secant.
    iv=G0*V+G2*V**3
    assert sp.diff(iv,V)==G0+3*G2*V**2
    assert sp.simplify(iv/V-(G0+G2*V**2))==0
    # Ionization creation minus attachment/recombination is ion storage.
    n,nu,src,att,beta,vol,pair=sp.symbols(
        "n nu src att beta vol pair",real=True)
    create=nu*n+src; remove=att*n+beta*n**2
    ndot=create-remove
    assert sp.expand(vol*pair*create-vol*pair*remove -
                     vol*pair*ndot)==0
    # Parallel resistors: one highly conductive element cannot bypass exterior.
    ch,outer=sp.symbols("ch outer",positive=True)
    eff=ch*outer/(ch+outer)
    assert sp.simplify(1/eff-(1/ch+1/outer))==0
    assert sp.limit(eff,ch,sp.oo)==outer
    return True


@dataclass(frozen=True)
class Parameters:
    # Dimensionally physical but deliberately synthetic reference circuit.
    channel_length_m:float=1.
    channel_radius_m:float=.01
    mobility_m2_Vs:float=1.
    exterior_resistance_ohm:float=1e6
    capacitance_F:float=1e-8
    load_conductance_S:float=1e-6
    ion_pair_energy_J:float=15.*E_CHARGE
    source_background_V:float=1e3
    source_ac_V:float=0.
    source_frequency_hz:float=10.
    source_delay_s:float=.001
    n_initial_m3:float=1e15
    spontaneous_pairs_m3_s:float=1e15
    ionization_rate_s:float=0.
    attachment_s:float=1.
    recombination_m3_s:float=1e-16
    controller_W:float=0.

    @property
    def volume(self):
        return math.pi*self.channel_radius_m**2*self.channel_length_m

def check_parameters(p):
    positive=(p.channel_length_m,p.channel_radius_m,p.mobility_m2_Vs,
              p.exterior_resistance_ohm,p.capacitance_F,p.ion_pair_energy_J)
    others=(p.load_conductance_S,p.source_frequency_hz,p.source_delay_s,
            p.n_initial_m3,p.spontaneous_pairs_m3_s,p.ionization_rate_s,
            p.attachment_s,p.recombination_m3_s,p.controller_W)
    if not all(math.isfinite(v) and v>0 for v in positive):
        raise ValueError("positive geometry/circuit/ion-energy required")
    if not all(math.isfinite(v) and v>=0 for v in others):
        raise ValueError("nonnegative finite rates/controls required")
    if not all(math.isfinite(v) for v in (p.source_background_V,p.source_ac_V)):
        raise ValueError("finite source waveform required")

def channel_conductance(n,p):
    return math.pi*p.channel_radius_m**2*E_CHARGE*p.mobility_m2_Vs*n/p.channel_length_m

def source_voltage(t,p):
    # Causal delayed EXOGENOUS source waveform; not an atmospheric time-of-flight
    # solution and not a controller-to-ionosphere echo receipt.
    return p.source_background_V+p.source_ac_V*math.sin(
        2*math.pi*p.source_frequency_hz*max(0.,t-p.source_delay_s))

def rates(t, state, p):
    v,n=state[:2]
    if n<0:raise ValueError("negative carrier density")
    gch=channel_conductance(n,p)
    if gch==0:
        i=0.
        heat_ch=0.
    else:
        resist_ch=1/gch
        i=(source_voltage(t,p)-v)/(p.exterior_resistance_ohm+resist_ch)
        heat_ch=i*i*resist_ch
    heat_exterior=i*i*p.exterior_resistance_ohm
    load=p.load_conductance_S*v*v
    vd=(i-p.load_conductance_S*v)/p.capacitance_F
    created=p.spontaneous_pairs_m3_s+p.ionization_rate_s*n
    disappeared=p.attachment_s*n+p.recombination_m3_s*n*n
    nd=created-disappeared
    ion_input=p.volume*p.ion_pair_energy_J*created
    ion_loss=p.volume*p.ion_pair_energy_J*disappeared
    natural=source_voltage(t,p)*i
    # Natural signed source work (may be negative), electrical channel/exterior
    # heat plus separately metered ionisation pump work, and controller overhead.
    return (vd,nd,natural,ion_input,p.controller_W,load,heat_ch,
            heat_exterior,ion_loss)

def residual_at(t,state,p):
    v,n=state[:2]
    vd,nd,wn,wi,wc,load,hch,hext,ionloss=rates(t,state,p)
    dU=p.capacitance_F*v*vd+p.volume*p.ion_pair_energy_J*nd
    return wn+wi+wc-load-hch-hext-ionloss-wc-dU

def simulate(p=Parameters(), duration_s=1., samples=160):
    check_parameters(p)
    if duration_s<=0 or samples<10:raise ValueError("duration/samples")
    from scipy.integrate import solve_ivp
    # First two states physical V and n; next seven states integrated work.
    y0=[0.,p.n_initial_m3]+[0.]*7
    def rhs(t,y):
        dy=rates(t,y,p)
        return list(dy)
    sol=solve_ivp(rhs,(0,duration_s),y0,rtol=2e-9,atol=2e-9,
                  max_step=duration_s/samples)
    if not sol.success:raise ArithmeticError(sol.message)
    end=sol.y[:,-1]
    v,n=end[:2]
    natural,ion,controller,load,ch,ext,ionloss=end[2:]
    initial=p.volume*p.ion_pair_energy_J*p.n_initial_m3
    final=p.capacitance_F*v*v/2+p.volume*p.ion_pair_energy_J*n
    residual=natural+ion+controller-load-ch-ext-ionloss-controller-(final-initial)
    return dict(phase_source_delay_s=p.source_delay_s,
                n_start=p.n_initial_m3,n_final=n,
                conductance_start_S=channel_conductance(p.n_initial_m3,p),
                conductance_end_S=channel_conductance(n,p),
                terminal_external_S=1/p.exterior_resistance_ohm,
                source_signed_J=natural,ionization_creation_pump_J=ion,
                controller_overhead_J=controller,load_J=load,
                bridge_heat_J=ch,exterior_heat_J=ext,
                ionization_loss_J=ionloss,storage_delta_J=final-initial,
                ledger_residual_J=residual,
                max_instantaneous_residual_J_s=max(
                    abs(residual_at(t,sol.y[:2,k],p)) for k,t in enumerate(sol.t)),
                valid='synthetic model, not source identity / measured solar work')

def run():
    exact_identity_checks()
    base=Parameters()
    controlled=Parameters(ionization_rate_s=5.,controller_W=2.)
    return dict(signed_ledger='Wnatural+Wion_creation+Wcontroller = Wload+Wchannel+Wexterior+Wion_loss+Wcontroller_aux+DeltaU',
       passive_foster='Debye g*s/(s+w), Lorentz alpha*s/(s²+gamma*s+Omega²): positive real for positive coefficients on real frequency; *not fitted waveguide*',
       source_condition='active source voltage explicitly specified, may be solar driven but NOT measured; delayed feedback is not automatically passive',
       no_added_ionization=simulate(base), controlled_ionization=simulate(controlled),
       hard_gates=['source_first P1/P2 R2/R3 still null','F10 full Maxwell PDE open',
                   'F13 actual multilayer waveguide and nonlinear plasma parameters open',
                   'F15 positive source-derived net over restored cycles open'])

if __name__=='__main__':print(json.dumps(run(),indent=2))
