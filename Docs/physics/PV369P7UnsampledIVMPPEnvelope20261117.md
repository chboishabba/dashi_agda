# P7 full sampled-IV MPP upper-envelope weld — 17 November 2026

**Primary programme:** independently measured >50% NET aperture-normalized solar electricity AND independently testable, nontrivial original-369 physical improvement against a conventional same-source device. No power gain follows from 369/SALC coordinate relabeling. Thermal, chemical and BH4 products remain separately booked; P3 RF, P4 multiple-pair, P5 optical 4T/2T, P6 biological and original corrected Bahder P1 remain active.

## Highest-alpha discovery and limitation of previous result

Existing `scripts/check_pv_g173_same_sample_optics_eqe_iv_weld.py` calculates exact maximum of **piecewise-linear interpolants** for each measured IV and a lossless series 2T prediction; `check_pv_369_worst_case_power_intervals.py` then bounded meter errors on those model MPP values. Neither alone proves that the **true physical MPP between sampled voltages** is no larger.

IEC [60904-1:2020](https://webstore.iec.ch/en/publication/32004) concerns PV illuminated IV measurement and explicitly recognizes steady-state and sweep transient/capacitive phenomena. [Fraunhofer ISE accredited calibration scope](https://www.ise.fraunhofer.de/content/dam/ise/de/downloads/service/callab/CalLab_PV-Cells_Overview_Accredited_Procedures.pdf) quotes *expanded* uncertainty for measured maximum power, and this is NOT a deterministic simultaneous absolute bound on an arbitrary true between-samples curve. Source paper/accountability and instrument sweep rate remain separate.

**Mathematical resolution conditional on actual full-interval monotonicity:** for a true nonnegative, nonincreasing steady-state generating current J(V), each sample-cell `V_i<=V<=V_{i+1}` has `0<=J(V)<=J(V_i)` and hence

```
P_sample_max = max_i V_i J_i
P_true_max   <= max_i V_(i+1) J_i = P_rectangle_upper
P_sample_max <= P_true_max
```

No interpolation shape assumption is needed, but the monotonicity of the **true continuous device response** must be source-witnessed; checking measured samples alone is insufficient. A changing illumination, hysteresis or a PV response with local non-monotonicities invalidates this particular certificate; it must not be used as a general unconditional bound.

**Demonstration on synthetic linear diode** `J(V)=510(1−V)`, `0<=V<=1`: true maximum 127.5 W/m²; point samples at 5/11/21/51/101/1001 voltage positions give upper rectangle bounds 191.25/153.00/140.25/132.60/130.05/127.755 W/m². The potential overstatement if an interpolating model assumes no unresolved maximum shrinks with mesh refinement. If the physical response is monotone, these bounds enclose the actual exact maximum for any grid. Separate independent Python checks of 36 mathematical inequalities on linear and nonlinear monotone curves passed. The committed `--selftest` script has not been run from a fresh GitHub checkout and no native Agda kernel is asserted.

## Implemented original-file round-trip

1. Modified the **original P5 measured producer** to write `declared_provenance.ordered_iv_sha256` for each junction, preserving its order. This is in addition to the existing original raw manifest and incident-solar digest, to prevent substitution/reordering of an IV.
2. New `scripts/check_pv_369_unsampled_iv_mpp_envelope.py`: physically constrained and SHA256-verified exact raw-IV reader, same-source P5 signed net-power crosscheck, monotonically sampled V↑/J↓, nonnegative generating currents and original Voc endpoint. For each curve, `P_sample_lower` and `P_rectangle_upper`, then conservative simultaneous lower/upper V/J meter uncertainties and converter eta envelopes and signed aux/drive/recovery costs, with a bounded source solar denominator. The original P5 *interpolant* MPP must lie between these source curve bounds (sanity). Results never claim IEC or laboratory certification. Declares `full_curve_monotonicity_evidence_declared` but `true_continuum_monotonicity_authenticated=false` unless independently verified outside this tool.
3. **Critical acceptance change:** `scripts/check_pv_369_worst_case_power_intervals.py` external P7 CLI now REQUIRES `--candidate-iv` for every candidate junction and `--control-iv` for a conventional matched control. It calls the new sweep certificate and replaces the older interpolant-only lower/upper values **before** evaluating strict >50% and strict 369-vs-control. The older internal `bound_receipt` synthetic selftest is retained as an illustration of meter arithmetic, NOT promotion-ready physical MPP validation. No candidate or control can pass the real-data P7 CLI while omitting its actual original raw and hashed IV files.
4. `DASHI/Physics/Photovoltaic/PV369UnsampledIVPowerEnvelopeExact.agda` imports original P5, P7, semiconductor spatial continuity/Scharfetter–Gummel and Motors Nat ≤, models an admitted rectangle upper bound and **source-dependent true-curve monotonicity** plus source-verified original-IV digest. `FullSweepRobustPVSourceWeld : Set₂` is correctly universe-polymorphic for carrying `Set₁` evidence. No physical source witness is inhabited and Agda Golden acceptance is OPEN. New import in the existing TOE PV splice; no ESD modifications.

## Exact source command

```bash
# First verify synthetic arithmetic only
python scripts/check_pv_369_unsampled_iv_mpp_envelope.py --selftest
python scripts/check_pv_369_worst_case_power_intervals.py --selftest

# For actual source-measured candidate + conventional independently
# source-specified complete IV sweeps, include full monotone source in
# uncertainty JSON. The same P5 raw hash manifest MUST match every IV.
python scripts/check_pv_369_worst_case_power_intervals.py \
  --candidate candidate_P5_optics_EQE_IV.json \
  --candidate-uncertainty candidate_full_sweep_bounds.json \
  --candidate-iv wafer369_iv1.csv wafer369_iv2.csv wafer369_iv3.csv wafer369_iv4.csv \
  --control conventional_P5_optics_EQE_IV.json \
  --control-uncertainty conventional_full_sweep_bounds.json \
  --control-iv control_iv1.csv control_iv2.csv control_iv3.csv control_iv4.csv \
  --output conditional_P7_acceptance.json

# Golden kernel acceptance in actual pinned repo toolchain
agda -i . DASHI/Physics/Photovoltaic/PV369UnsampledIVPowerEnvelopeExact.agda
agda -i . DASHI/Unified/PVPrimaryTOESpliceExact.agda
```

The additional bound JSON field `monotone_full_IV_source` must cite a defensible physical **full-sweep** proof/measurement, including transient/rate effects. A string alone is not certified physical monotonicity; this is the unavoidable source-fibre gate. A real arbitrary I–V curve may require a different physical upper-bound method, like source-backed interval derivative and curvature bounds or dense continuous MPPT sweeps.

## Roadmap/impact

**P5 pointwise spectral and electrical consistency:** implemented but original actual same-specimen data not supplied. **P7 conditional unsampled MPP bound:** source-written and independently crosschecked on synthetic functions; kernel and actual physics OPEN. **P7 separate real same-spectrum 369 improvement > conventional control:** OPEN. **Original 369-specific physical operator prediction:** still OPEN; must not be inferred from a changed basis. **>50 independently verified net solar-electric:** still OPEN.

**Next highest-alpha:** (i) obtain an actual four-/five-junction raw source dataset with measured optical R/T/A and EQE and calibrated I–V sweep, meter and simulator uncertainties; (ii) prove or measure full-sweep steady-state validity and verify unsampled continuum MPP bound; (iii) source-construct 369-distinct actual material operator and preregister polarisation/angle/EQE predictions, matched with conventional no-369 control; (iv) continue P1 corrected Bahder QW, P3 active, P4 multiplication, P6 BH4 independently.
