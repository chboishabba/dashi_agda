# R2P2 mountain optical-clock comparison: source, reused proofs, and empirical boundary

## O — Objective

Formalise the supplied Veritasium transcript as a source-typed R2P2 optical-clock observation request. Do not infer quantum gravity from conventional gravitational redshift, or infer a finished clock comparison from a working optical link.

## R — Reuse-first audit (master at 9055f975, checked 2026-10-28)

- Reuse DASHI/Physics/Closure/QuantumClockProperTimeRedshiftBridge.agda for Δf/f ≈ ΔU/c² and local uniform-field ΔU ≈ gh. These are approximate physical laws with named assumptions, not newly derived here.
- Reuse DASHI/Physics/Closure/QuantumClockEmpiricalRedshiftReceiptRequest.agda for experiment identity, measurements, covariance/systematics and SI/consumer evidence gates.
- Reuse DASHI/Physics/Closure/BothwellYe2022MillimetreRedshiftReceipt.agda for the physically DIFFERENT 2022 millimetre-scale strontium clock sample.
- Reuse DASHI/Physics/Closure/QuantumClockSIObservableBridge.agda, QuantumClockDimensionlessObservableLaw.agda and the existing SI constants registry.
- Prior repository lineages: PR #1085 (merged); PR #1117 (open, optical geodesy and evidence ingestion); PR #1292 (open, TOE quantum metrology). Branch-only results from #1117 and #1292 are not imported.
- Latest unrelated example PRs #1404–#1406 demonstrate source/claim-gate discipline, not new R2P2 experimental evidence.

## Primary scientific roots and priority

1. Einstein's equivalence principle and relativistic redshift (1907–1915) are historical GR antecedents; the redshift law is inherited, not a DASHI discovery.
2. Pound and Rebka (1959–1960), Vessot et al. Gravity Probe A (1980), Chou et al. optical clock elevation (2010), and Bothwell et al. (2022) are independent prior experimental roots.
3. Hall, Hänsch and colleagues developed frequency-comb optical metrology in the late 1990s and 2000. Hall/Diddams/Jones and Holzwarth/Udem/Hänsch contributions retain their distinct priority.
4. APS DAMOP 2026 oral abstract (Theodora Triano, Laura Sinclair, Andrew Ludlow, Emily Caldwell and R2P2 collaborators): https://meetings-archive.aps.org/damop/2026/g07/7/ . This is the PRIMARY experimental source for the R2P2 network, not the video.
5. NIST optical-comb description: https://www.nist.gov/pml/time-and-frequency-division/popular-links/time-frequency-z/time-and-frequency-z-f . Original frequency comb work: https://www.nist.gov/publications/stabilizing-and-measuring-optical-frequencies .
6. BIPM current SI second and defining constants: https://www.bipm.org/en/si-base-units/second . The cesium-133 definition is exact at 9,192,631,770 Hz; an optical ytterbium frequency is not thereby the current defining SI second.
7. Bothwell et al., Nature 602, 420–424 (2022), https://doi.org/10.1038/s41586-021-04349-7 . Their strontium sample and R2P2's two separated ytterbium clocks are distinct objects.

## C — New finite adapter and numerical check

New owner: DASHI/Physics/Closure/R2P2MountainOpticalClockComparisonExact.agda.

The APS abstract describes two neutral Yb lattice clocks at about 4300 m and 1650 m elevation; a network with 69 km free-space plus 81 km fibre; an August 2025 phase-continuous shakedown with instability of a few parts in 10^-17 at ~100 s; and further characterisation targeting 10^-18-class link metrics. Published clock result, final redshift residual and independent uncertainty replay are not provided by this abstract.

The 4300 m and 1650 m elevations differ by 2650 m at their stated rounding, while the same abstract quotes an approximately 2700 m elevation difference. This is NOT an independent survey error. Both inputs are rounded. The transcript's ~80 km line-of-sight path and the APS-described 69 km free-space component should not be silently treated as the same measured distance.

The supplied transcript quotes a predicted fractional slope of 2.885×10^-13. Treat that number as VIDEO-SOURCED pending the published independent geopotential-calculation product. The exact arithmetic is:

    (2885 / 10^16) × 86400 seconds/day = (249264000 / 10^16) seconds/day
      = 24.9264 nanoseconds/day.

The local finite equality is an exact Agda arithmetic witness. It does not certify the physical prediction. A revised geopotential model could change the fitted expected slope without changing this arithmetic.

## Optical-comb correction

An indexed comb tooth is ν_n = n f_rep + f_CEO. With a measured nonnegative beat, ν_opt = ν_n + f_beat or ν_n = ν_opt + f_beat, according to the side of the tooth. The transcript's simplified n f_rep + beat formula does not mention f_CEO. That omission is safe only after an explicit zero-offset or calibrated-offset assumption.

The new module uses two distinct record types for the upper and lower beat branches. The examples use n=3, f_rep=10 Hz, f_CEO=2 Hz, f_beat=4 Hz, and ν_opt=36 Hz / 28 Hz. These small numbers are SYNTHETIC witnesses only. They are not clock data or a claim that such a mode index applies to a real ytterbium lattice clock.

## S/L — Source and claim discrimination

| Claim | Evidence accepted here | Missing for stronger promotion |
| --- | --- | --- |
| SI second uses Cs-133 hyperfine constant | BIPM authority | Nothing for the definition; physical realization has its own uncertainty |
| Weak-field redshift relationship | Existing repository symbolic bridge and standard GR | Model/worldline calibration for R2P2 |
| Optical comb needs f_CEO and a signed beat branch | NIST source and finite Agda arithmetic | Actual calibrated comb mode index and frequency logs |
| R2P2 long hybrid link operated in August 2025 | APS 2026 meeting abstract | Link raw stream, calibration, independent replay |
| Final two-clock redshift ratio differs from/equals GR at a declared uncertainty | NOT established by these inputs | Clock-systematic budget, link transfer, geopotential and covariance, frozen analysis |
| Gravity is quantum / GR fails | NOT established | An experiment discriminating competing gravitational dynamics, including quantum alternatives |

Distinguish phase-continuous transfer and fractional link instability from total clock accuracy. Atmospheric turbulence, nonreciprocity, cycle slips, local gravity/tidal corrections, geodesy, and two clocks' systematic biases are separate evidence debts. A demonstration of coherent optical transfer is not automatically an Einstein or quantum-gravity test result.

## P/G/F — Ownership, verification and future debt

- SOURCE-OWNED: Einstein/Pound–Rebka/Vessot/Chou/Bothwell scientific antecedents; Hall/Hänsch/Diddams optical-comb construction; BIPM metrological definition; R2P2 optical network, apparatus and measurements.
- PRIOR DASHI-OWNED: canonical redshift, dimensionless law, SI-second/observable gates, Bothwell/Ye receipt, empirical request, and PR #1117/#1292 branch work (not merged into this branch).
- NEW SOURCE-WRITTEN DASHI WORK: this R2P2 attributed evidence adapter, the two finite comb branch examples, transcript arithmetic, and import graph connections.
- NUMERICAL CHECKS: exact rational 24.9264 ns/day; small signed-beat arithmetic examples. Neither is evidence for an R2P2 measured signal.
- KERNEL STATUS: the source has not been checked by the Agda kernel in this work session. Only a successful Agda invocation against the exact PR head can change this claim.
- EMPIRICAL STATUS: published APS abstract supports only its stated shakedown. No raw, checksummed clock data or independently reproduced final gravity residual was ingested.
- EXISTING IBRAHIM/MONSTER 3B OWNERSHIP: untouched. No optical-frequency coincidence, spectral pattern or analogy identifies a Monster representation.
- PARETO MAX-CUT: the useful addition is source-specific R2P2 evidence and comb sign/offset bookkeeping. Do not copy entire optics or GR formalisms or construct a new claim-promotion gate.
- SNOWBALL: when a final data article and archive appear, link hash-pinned raw data, clock systematic/covariance file, calibration geodesy, independent replay, and finally only the claim supported by that result.

## Follow-up verification commands

    python3 tests/test_r2p2_mountain_optical_clock.py
    agda -i . -i <path-to-matching-agda-stdlib> DASHI/Physics/Closure/R2P2MountainOpticalClockComparisonExact.agda

Then type-check the two canonical TOE roots at the same exact commit, with the repository's pinned toolchain. No ESD file was modified.
