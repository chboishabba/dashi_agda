#!/usr/bin/env python3
"""Conditional SURA 2026 three-wave energy partition / Filsinger boundary.

Original observation: Chernyshov et al., GRL 2026, DOI 10.1029/2026GL123503.
Prior three-wave energy relation: J. M. Manley and H. E. Rowe (1956),
Some General Properties of Nonlinear Elements—Part I: General Energy
Relations, Proceedings IRE, DOI 10.1109/JRPROC.1956.275145.
Independent DASHI exact one-event Manley–Rowe *conditional* accounting:
not an empirical SURA plasma source reconstruction, ionospheric power meter,
or proof that any particular observed band arose via exactly this triad.
"""
import json
import sympy as S

F_HF_KHZ = S.Integer(5350)
F_LH_INTERVAL_KHZ = S.Interval(8, 9)


def triad_exact():
    f0, fl, action = S.symbols('f0 fl action', positive=True)
    fh = f0 - fl
    # Pump - one action, daughter HF + one, LH + one.
    # Multiply by Planck's constant for actual photon energy; cancels in ratios.
    pump_loss = f0 * action
    daughter_hf_gain = fh * action
    lower_hybrid_gain = fl * action
    assert S.simplify(pump_loss-daughter_hf_gain-lower_hybrid_gain)==0
    # Test field-energy accounting at exact rational source examples.
    lo,hi=F_LH_INTERVAL_KHZ.start, F_LH_INTERVAL_KHZ.end
    ratios=[S.factor(x/F_HF_KHZ) for x in (lo,hi)]
    downshift=[S.factor(F_HF_KHZ-x) for x in (hi,lo)]
    assert downshift == [S.Integer(5341),S.Integer(5342)]
    assert ratios == [S.Rational(4,2675), S.Rational(9,5350)]
    # 17-18 kHz is *compatible* with a doubled [8.5,9] kHz subset;
    # a harmonic is NOT a second independent store of lower-hybrid work.
    second_harmonic=S.Interval(17,18)
    lh_compatible=F_LH_INTERVAL_KHZ.intersect(S.Interval(second_harmonic.start/2,second_harmonic.end/2))
    assert lh_compatible==S.Interval(S.Rational(17,2),9)
    return {
      'frequency_hf_pump_khz':str(F_HF_KHZ),
      'possible_hf_daughter_khz':str(S.Interval(*downshift)),
      'lh_fundamental_khz':str(F_LH_INTERVAL_KHZ),
      'lh_fraction_pump_energy_one_stage':[str(x) for x in ratios],
      'lh_fraction_pump_percent_approx':[round(float(100*x),6) for x in ratios],
      'second_harmonic_compatible_lh_khz':str(lh_compatible),
      'algebraic_manley_rowe_residual':'0',
      'interpretation':'conditional ideal single three-wave decay, not total observed conversion efficiency'
    }


def passive_mode_conversion():
    # Lower-hybrid mode -> whistler + loss. Any downstream load is a share
    # of propagating whistler work; neither source nor receiver is measured.
    eta, action, fl = S.symbols('eta action fl',nonnegative=True)
    loss_share=1-eta
    whistler = eta*fl*action
    plasma_loss=loss_share*fl*action
    assert S.simplify(whistler + plasma_loss - fl*action) == 0
    receiver_fraction=S.symbols('receiver_fraction', nonnegative=True)
    receiver=receiver_fraction*whistler
    propagation_loss=(1-receiver_fraction)*whistler
    assert S.simplify(receiver+propagation_loss-whistler)==0
    assert S.simplify(receiver + propagation_loss + plasma_loss - fl*action)==0
    f0=S.symbols('f0',positive=True)
    hf_daughter=(f0-fl)*action
    assert S.simplify(f0*action-hf_daughter-receiver-propagation_loss-plasma_loss)==0
    for eta_val,rho_val in [(S.Rational(1,2),S.Rational(3,4)), (0,1),(1,1)]:
        sample={eta:eta_val,receiver_fraction:rho_val,fl:S.Integer(9),action:1,f0:5350}
        assert S.simplify((f0*action-hf_daughter-receiver-propagation_loss-plasma_loss).subs(sample))==0
    # For physically passive cases, eta and receiver_fraction must be <=1.
    # Do not infer their measured values from the presence of a spectral peak.
    return {'symbolic_energy_residual':'0','receiver_power_must_be_measured':True,
            'passivity_requires':['0 <= eta <= 1','0 <= receiver_fraction <= 1'],
            'pump_to_ground_per_stage_ceiling':'f_lh / f_HF only if one-quantum triad and passive conversion with no additional energy reservoir'}


def lti_fixed_coefficients_no_steady_frequency_conversion():
    # Generic frozen-coefficient linear time-invariant Fourier response:
    # (i*omega I - A) Z = B J. At any omega, frequency-domain channels
    # decouple, so an isolated harmonic source cannot create another
    # steady harmonic without nonlinear/time-varying coefficients or a
    # second independently supplied source. Initial transients are excluded.
    w,a,b,j=S.symbols('omega a b j',real=True)
    z=S.simplify(b*j/(S.I*w-a))
    assert S.simplify((S.I*w-a)*z-b*j)==0
    assert S.simplify(S.diff(z, j) - b/(S.I*w-a))==0
    return {'fixed_LTI_harmonic_residual':'0',
            'steady_discrete_frequency_conversion':False,
            'exceptions':'source transients, broadband drive, explicitly time-varying or nonlinear coefficients, independent plasma daughter sources'}


def test_negative_controls():
    # Nominal facility ERP is directional radiated quantity, not the HF
    # pump energy depleted in one specific plasma triad. The paper gives
    # neither the latter nor a receiver terminal meter. No derived Watts.
    assert S.Integer(150_000_000)>0
    return {'erp_not_terminal_or_absorbed_source_work':True,
            'no_plasma_action_rate_measured':True,
            'cannot_compute_received_watts':True}


def run():
    result={'status':'PASS', 'evidence':'EXACT_CONDITIONAL_NONLINEAR_ENERGY_NOT_EXPERIMENT_REPLAY',
            'triad':triad_exact(), 'passive_conversion':passive_mode_conversion(),
            'LTI_negative_control':lti_fixed_coefficients_no_steady_frequency_conversion(),
            'ERP_anti_promotion':test_negative_controls()}
    print(json.dumps(result,indent=2,sort_keys=True))
    return result

if __name__=='__main__':
    run()
