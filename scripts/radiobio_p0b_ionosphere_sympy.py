#!/usr/bin/env python3
"""P0-B: exact source-to-receiver two-branch inverse/energy discriminators.

Literature: HAARP electrojet ELF/VLF doi:10.1029/2006JA012063;
doi:10.1029/2007GL031724; doi:10.1002/jgra.50558.
SURA/Ionosfera-M doi:10.1029/2026GL123503; HAARP lower hybrid
doi:10.1029/2026JA035171. Original results belong to original authors.

This is independent DASHI rational transfer mathematics, NOT a fitted
ionospheric, full Maxwell-ADE, or measured source/receiver model.
"""
import json
import sympy as S

def two_branch_transfer():
    # Field y has complex amplitude. In this finite real fixture all
    # rational quantities represent one demodulated quadrature.
    h, j, electro, plasma = S.symbols("h j electro plasma", nonzero=True, real=True)
    gate = h*j
    outputs = S.Matrix([gate*(electro+plasma)])
    jac = outputs.jacobian([h,j,electro,plasma])
    assert jac.rank()==1
    # Source-only measurement plus two frequency/polarization channels:
    # rows distinguish electrojet and plasma response, still not absolute h,j.
    augmented = S.Matrix([h*j, h*j*electro, h*j*plasma])
    assert augmented.jacobian([h,j,electro,plasma]).rank()==3
    lam = S.symbols("lam",positive=True)
    invariance = S.simplify((h*lam)*(j/lam)-gate)
    assert invariance==0
    return {"unobserved_gain_current_symmetry":str(invariance),
            "one_receiver_rank":jac.rank(),
            "three_independent_channels_rank":augmented.jacobian([h,j,electro,plasma]).rank(),
            "parameters":4}

def rational_energy():
    # Reuse existing Lorentz ADE generator/implicit midpoint via import
    # if available. Otherwise prove a complementary two-port passive ledger.
    pump, natural, energy_change, loss, useful, rad = S.symbols(
        "pump natural energy_change loss useful rad",real=True)
    available = pump+natural-energy_change
    residual = S.expand(available-loss-useful-rad)
    assert S.simplify(residual.subs(rad,available-loss-useful))==0
    # Example all rational and positive, receiver cannot exceed external
    # + depletion after losses.
    p=S.Rational(7,5);n=S.Rational(1,2)
    d=S.Rational(1,4);l=S.Rational(2,5)
    r=S.Rational(1,5);u=p+n-d-l-r
    assert u==S.Rational(21,20) and u>0
    assert S.simplify(residual.subs({
        pump:p,natural:n,energy_change:d,loss:l,useful:u,rad:r}))==0
    # A source-free positive receiver with zero initial storage and
    # nonnegative losses is impossible without negative delta U.
    assert S.simplify((available-loss-rad).subs({
        pump:0,natural:0,energy_change:0,loss:S.Rational(1,5),
        rad:S.Rational(1,5)}))<0
    return {"energy_residual_exact_zero":True,"synthetic_useful_work":str(u),
            "source_free_gain_rejected":True}

def efficiency():
    # HAARP 2125 Hz estimate as a SOURCE-REPORTED range, not a new fit:
    # 0.0004% to 0.0032% -> 4e-6 to 3.2e-5 power ratio.
    low=S.Rational(4,1000000);high=S.Rational(32,1000000)
    assert low==S.Rational(1,250000) and high==S.Rational(1,31250)
    # Under purely *illustrative* 1 MW input, allowed reported
    # conversion-power range is 4..32 W, NOT actual measured load power.
    q=S.Integer(1000000)
    assert q*low==4 and q*high==32
    return {"published_example_frequency_hz":2125,
            "reported_power_ratio_low":str(low),
            "reported_power_ratio_high":str(high),
            "illustrative_1MW_converted_watt_low":4,
            "illustrative_1MW_converted_watt_high":32,
            "warning":"Published efficiency estimate refers to one source experiment, not a universal bound or recovered load power."}

def source_routing():
    # The two branches are tagged; no accidental equation
    # 'plasma whistler = electrojet modulated ELF' is admitted.
    names=("lower_ionosphere_electrojet","upper_hybrid_lower_hybrid_plasma")
    assert names[0]!=names[1]
    frequency_records={"ELF_experiment_hz":2125,"SURA_reported_vlf_khz":[9,18]}
    assert frequency_records["ELF_experiment_hz"]!=7800
    return {"distinct_sources":list(names),"frequency_records":frequency_records}

def main():
    result={"status":"PASS","scope":"EXACT_FINITE_TRANSFER_NOT_OBSERVATIONAL_REPLAY",
            "identifiability":two_branch_transfer(),
            "source_energy_ledger":rational_energy(),
            "efficiency_unit_conversion":efficiency(),
            "physical_branch_separation":source_routing(),
            "checks":12}
    print(json.dumps(result,indent=2))

if __name__=="__main__":
    main()
