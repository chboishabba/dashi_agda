# P5/P7 same-sun PV >50% loss frontier — 17 November 2026

Source branch: draft [DASHI PR #1523](https://github.com/chboishabba/dashi_agda/pull/1523). The user-defined goal remains **independent net solar-to-electric conversion >50% AND an experimentally distinguishable original 369-derived physical advantage**. Thermal/chemical/fuel outputs are separately accountable auxiliaries; driver electricity must be deducted. Reuse original atomic/SALC/Kane and semiconductor optics, and keep P3 RF, P4 multiplication, P5 optical routing and P6 BH4 biological branches live.

## Source, model and published comparator

**Original same-sun model owner:** `scripts/check_pv_astm_g173_radiative.py`, NLR ASTM G173-03, 2,002 rows, 1000.3706555734 W/m² globally integrated; prior numerical multistart model with optimised gaps, lossless step absorbers, one radiation hemisphere, 298.15K, 2T current-matched versus 4T independent electrical extraction. **None of these numerical model optima is a mathematically certified global upper bound**. This file does NOT reoptimise and must not infer an uncertainty interval around the prior solver.

**Independent published experimental comparator:** M. Green et al., *Solar cell efficiency tables: Version 68*, Joule 10 (2026), 102494, [DOI 10.1016/j.joule.2026.102494](https://doi.org/10.1016/j.joule.2026.102494), records 35.2% for a one-sun 2T perovskite/Si tandem and 47.6% at 665× for a four-junction bonded CPV cell. The **different concentrator spectrum/normalization and actual architecture make direct subtraction from our one-sun ideal models invalid**. A certified 47.6% concentrator is not evidence that a modelled 56% one-sun 4T is attainable.

## Exact arithmetic loss frontier under a common denominator

Values taken unchanged from the previous one-sun model (percent of incident aperture sunlight); `Δ_loss,pp=η_ideal,model−50%`. A *strict* >50% model only survives if the **sum of all losses in incident-solar percentage points is strictly LESS than Δ_loss,pp**. A tie at exactly 50.000% is a failure, not success. Modelled gross energy, no real module.

| Architecture | Prior model ideal | pp of loss tolerance | W/m² loss tolerance @ G173 | ideal output loss budget | Status |
|---|---:|---:|---:|---:|---|
| 2T 1J | 33.773% | none (shortfall 16.227pp) | none | 0% | Cannot reach 50 without an independently quantified physical upgrade |
| 2T 2J | 45.824% | none (shortfall 4.176pp) | none | 0% | Same |
| 2T 3J | 51.741% | 1.741 | 17.416 | 3.365% | Very narrow conditional model budget |
| 4T 3J | 51.867% | 1.867 | 18.677 | 3.600% | Extra converter/contact overhead must be paid |
| 2T 4J | 52.162% | 2.162 | 21.628 | 4.145% | Tight even before fabrication |
| **4T 4J** | **56.077%** | **6.077** | **60.793** | **10.837%** | Larger conceptual margin, more terminals/complexity |
| 2T 5J | 53.553% | 3.553 | 35.543 | 6.635% | Current matching/local-optimiser sensitive |
| **4T 5J** | **58.532%** | **8.532** | **85.352** | **14.577%** | Largest of the listed conditional model margins |

**Priority inference, not physical recommendation:** 4T 4J and 4T 5J have larger *model* headroom than 3J 2T; that makes them better initial **loss-budget discriminators**, not proven more practicable physical architectures. 4T architecture must include extra spectral splitting/optical leakage, separate-contact series resistance, independent converters, interconnection/cost and aperture-normalised parasitic absorption. A conventional 4T optimisation may not share absorptance or bandgap constraints with a 2T stack.

**One explicit model-only 4T4J budget:** optical/parasitic 1.000pp; nonradiative 1.500pp; converter/current mismatch 0.900pp; contacts 1.000pp; thermal/auxiliary 1.676pp; total 6.076pp; net 50.001pp, *strictly* positive by 0.001pp. One further 0.001pp of loss creates a tie and FAILS. This is not a measured material-loss estimate: all entries are CHOSEN examples and are not independently sourced. The 2T3J analogue loses 1.740pp leaving 50.001pp.

**Negative controls:** 1J/2J with baseline model <50% have *positive shortfalls*, not negative loss budgets; a negative-loss input is explicitly rejected. For matched 4T4J vs 2T4J, a large 4T converter/optical cost can reverse the model advantage; contact count is no free gain. Other source-independent numerical arithmetic tests verify one-unit strict tie-failure and additive loss denominators; no actual device model acceptance is claimed.

## Exact Agda and original TOE reuse

New `DASHI/Physics/Photovoltaic/PV369G173MultiJunctionLossFrontierExact.agda` imports the ORIGINAL motor Nat ≤ proof, `PV369NetHalfThresholdExact` and original PV energy source already attached to the TOE root. It stores all ten published-model numbers as *scenario constants*, a same-source loss partition record with mandatory sum-equality and `suc(50000) ≤ net` strict model threshold. Two concrete arithmetic witnesses (2T3J and 4T4J) establish only **model threshold arithmetic**. The inherited `successorNotLeItself` proves exactly-half ties cannot pass. The current PR is NOT Agda-kernel checked. No measured device is instantiated and no P7 experiment is closed.

The source/validation script `scripts/check_pv_g173_multijunction_net_loss_frontier.py` calculates exact Fraction arithmetic for all ten scenarios and rejects physically nonsensical negative losses; its source was committed but **not executed from a fresh GitHub checkout**. An independently executed equivalent in-session calculation verified 60 arithmetic cases, all passed. These are math-only, not material measurements or original spectrum reoptimization.

## Max-cut next gates

1. **P5 strong physical candidate:** bound 4T 4J or 5J losses from actual measured source reflectance/absorptance, measured terminal conversion/converter overhead and temperature-specific real junction I-V. Compare 2T 3J/4J current-matching on SAME optical distribution, instead of comparing independent theoretical optima alone. Build a 4T control without 369 first.
2. **P1 P2 369 predictive requirement:** actual same-material change in operator/charge extraction beyond a pure Fourier/SALC basis transform; strain/QW source 8-band Bahder corrected operator and measured PLE/absorption are still unresolved. Do not claim >50 because 369 is present.
3. **P3 P4:** compare measured RF driver energy against extra MPP electrical work, and actual multiexciton extraction at useful voltage vs Auger/thermal losses.
4. **P6:** photosystem BH4-sourced absorption/electron transport/fuel/product ledger remains separate; don't add biofuel LHV to an electrical numerator.
5. **P7 terminal gate:** independently measured strict net electric >50% aperture-normalised SAME standard source, period, thermal/aux/driver boundaries AND strict 369-vs-conventional matched net gain. Both records remain uninhabited; string provenance fields alone cannot externally authenticate an experiment. Agda typechecking cannot substitute for laboratory authentication.

**Acceptance:** Local numerical fractional-grid computations passed (60 independent arithmetic checks); source-written exact Agda still **OPEN** under local Golden acceptance, and original ideal multijunction numerical gap search remains a non-certified heuristic optimisation.
