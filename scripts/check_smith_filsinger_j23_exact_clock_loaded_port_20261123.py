#!/usr/bin/env python3
"""J23 exact clock + *separate isolated linear loaded-port* critical-match test.

Original nonlinear nine-state orbit and interval ODE existence are NOT proved
by this symbolic reduction. Source-only, synthetic externally prescribed wave.
"""
import json
import sympy as s

def run():
    t,phi=s.symbols('t phi',real=True)
    omega=s.Rational(11,10)
    native_T=20*s.pi
    tau=2*s.pi/omega
    assert s.simplify(11*tau-native_T)==0
    assert s.simplify(omega*native_T-22*s.pi)==0
    assert s.simplify(s.cos(omega*(t+tau)+phi)-s.cos(omega*t+phi))==0
    assert s.simplify(s.sin(omega*(t+tau)+phi)-s.sin(omega*t+phi))==0
    assert s.simplify(s.sin(tau))!=0  # controller sin(t) cannot use tau

    # Isolated LINEAR one-port surrogate: loaded damping cannot be omitted.
    gr,gi,gl,gp=s.symbols('gamma_r gamma_i gamma_load gamma_parasitic',positive=True)
    Gamma=gi+gl+gp
    reflection=s.factor(((Gamma-gr)/(Gamma+gr))**2)
    capture=s.factor(4*gr*Gamma/(Gamma+gr)**2)
    useful=s.factor(4*gr*gl/(Gamma+gr)**2)
    assert s.simplify(reflection+capture-1)==0
    assert s.simplify(useful-capture*gl/Gamma)==0
    derivative=s.factor(s.diff(useful,gr))
    assert s.simplify(derivative-4*gl*(Gamma-gr)/(Gamma+gr)**3)==0
    optimal_gr=Gamma
    max_useful=s.factor(useful.subs(gr,optimal_gr))
    assert s.simplify(max_useful-gl/Gamma)==0
    assert s.simplify(1-max_useful-(gi+gp)/Gamma)==0
    assert s.simplify(reflection.subs(gr,optimal_gr))==0

    # Native non-linear HF capacitor's exact pointwise work identity.
    ch,alpha,x,ih,ga,rc,rg,on,b,kh,u,Lh=s.symbols(
        'Ch alpha x ih Gload Rcoil Rgap on b kh u Lh',real=True)
    q=ch*(x+alpha*x**3)
    ec=ch*(x**2/2+s.Rational(3,4)*alpha*x**4)
    xd=(ih-ga*x)/s.diff(q,x)
    assert s.simplify(s.diff(ec,x)*xd - (x*ih-ga*x*x))==0
    return dict(status='J23_EXACT_SYMPY_LOCAL_PASS',
       sympy_version=s.__version__,
       exact_source_omega='11/10',exact_fundamental_tau='20*pi/11',
       source_periods_per_native_window=11,
       source_harmonics_preserved_under_tau=True,
       controller_sine_preserved_under_tau=False,
       linear_port_reflection=str(reflection),
       linear_port_capture=str(capture),
       linear_port_useful_load_fraction=str(useful),
       optimal_loaded_radiative_damping=str(optimal_gr),
       max_linear_port_useful_fraction=str(max_useful),
       finite_parasitic_or_internal_loss_excludes_unity=True,
       nonlinear_capacitor_pointwise_identity=True,
       nonlinear_nine_state_optimum_established=False,
       validated_interval_periodic_orbit_established=False,
       physical_source_or_hardware_established=False,
       github_actions_or_ci_run=False)

if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
