# PR #1242 max-cut: correcting S1 statistics, source joins, and S6 rank conditioning

**25 October 2026 (Brisbane) · scientific/statistical repair, not a laboratory experiment.**
This is the next concrete evidence obligation following the [20-scientist and field-control audit](psychotronics-s1-s6-twenty-scientist-maxcut-20261024.md). All new work here is **DASHI engineering/mathematical adaptation** of established metrology/statistical tools and previously attributed science. The original Amy Eskridge historical talk, Li/Torr, Podkletnov, POAMS, McCasland and Ren/Dong/Fang research maintain **distinct original authorship and historical/experimental status**.

## Identified concrete defects in the previous PR head

1. **False independent repeats in S1:** `psychotronics_field_loom_metrology.py` previously added each pair's magnetic moment uncertainty to diagonal variance, then averaged as though the calibration were independently regenerated at every pair. Multiple measurements of a single magnet with the **same calibration** cannot reduce the shared error as `1/√N`. The old total-error representation was therefore optimistic for correlated calibration.
2. **Incomplete source-object weld:** a raw-file SHA-256 and a calibration-file SHA-256 only identify two bags of bytes. The analysed `pairs` could be independently written and unrelated to either. The old `submission_ready_for_independent_metrology_review` checklist did not establish a source-to-analysis same-object mapping.
3. **Inadequate polarity design receipt:** the existing `polarity_factorial_verified` was a metadata Boolean without an independently computed identifiability test. Switching coil-on/off with the same dipole orientation cannot separate coil-only signals, true dipole×coil force, and current-even heating effects.
4. **Potential cancellation in S6:** obtaining the smaller squared singular value of the 2-column response matrix from `(trace-√discriminant)/2` is unstable near rank one. That is exactly the crucial region for a midplane-sensor null or rank-one negative control. Existing outputs were reproduced with independent NumPy SVD; this repair protects adversarial near-singular inputs.

## Implemented solutions and exact interfaces

### S1 correlated residual / GLS

[Correlated GLS module](../../scripts/psychotronics_field_loom_covariance.py) and [S1 entrypoint](../../scripts/psychotronics_field_loom_metrology.py) now use an explicitly structured covariance model. Let the per-pair signed residual `r_i = (F_on - F_off)_i - m_i(∂B_on-∂B_off)_i` and `g_i` the measured gradient difference; the special fixed point-dipole assumptions remain necessary.

```text
C_ij = δ_ij σ²_ind,i
     + δ_group(i,j) u²_m,group · g_i · g_j
     + u²_F,common
     + u²_scale,common · (m_i g_i)(m_j g_j)
w = C⁻¹ 1 / (1ᵀ C⁻¹ 1)
r_GLS = Σ w_i r_i
Var(r_GLS) = (1ᵀ C⁻¹ 1)⁻¹
```

The algorithm uses standard-library Cholesky and reports **separately** independent random noise, group-shared dipole-moment uncertainty, common force offset and common field-scale error. Its `moment_calibration_id` applies identical moment and standard uncertainty to an entire correlated group; conflicting values for one ID cause failure. Groups with different IDs are treated as independent **only conditionally** on a separately justified provenance claim. The maximum pair floor cannot undercut the floor in a matching calibration document.

**Independent local numerical spot-check:** 16 repeats with `σ_ind=2×10⁻⁷ N`, shared `u_m=0.001 A·m²` and `g=−0.01 T/m`, shared offset `u_F=4×10⁻⁶ N` produce combined `σ≈1.0770445673×10⁻⁵ N` (NumPy covariance solution). Naively treating the `u_m g` term as independent would report a much smaller uncertainty. This is an independent **mathematical cross-check**, not an executed GitHub source-blob test and not an experimental outcome.

The statistical estimator is **conditional** on Gaussian/linearised error propagation, constant residual and the specified correlation model. It is *not* a discovery p-value or proof that the ordinary physical model includes all thermal, mechanical, constitutive or environmental forces. With changing magnetisation, induced susceptibility, ferrofluid fluid mechanics, ferromagnetic hysteresis or superconducting response, the **point-fixed-dipole law itself must be replaced** before this tool can be used.

### S1 source replay versus authentic observation

[Same-object source replay](../../scripts/psychotronics_field_loom_source_join.py) checks bounded, hashed **pair JSON**, hashed **calibration JSON**, the connected **instrument source-stream file hash**, exact equality of parsed source pairs to the analysed pair list, apparatus/configuration/serial/revision identity, moment-calibration group entries and the stated common systematic floor. It refuses hash mismatch or mutated analysis rows and reports the calibration floor for the downstream GLS.

**Ceiling:** this is *same-byte/source-identity consistency only*. It does **not** prove that the source-stream bytes came from a real instrument, that the pairs were actually computed from that stream (still a separate reducer/version and re-execution requirement), that a witness independently reviewed a calibration, or that an event is physically extraordinary. `raw_to_pairs_reducer_verified` is an additional intake condition but remains **self-declared in this revision**; its underlying transformation function and executable replay need independent validation. `submission_ready_for_independent_metrology_review` means the user's *self-declared evidence dossier* passes structural checks, **not** that a laboratory, institution or referee has accepted any measurements. `gravitational_result_admissible` is hard **false**.

### S1 factorial identification

[Exact rational rank](../../scripts/psychotronics_field_loom_factorial.py) reuses the pre-existing `psychotronics_design_rank_audit.rank_exact` over five deliberately separate columns:

```text
[1, coil_sign, dipole_sign, coil_sign*dipole_sign, coil_sign**2]
```

Six ideal arms `coil ∈ {-1,0,+1}` crossed with `moment polarity ∈ {-1,+1}` have rank **5**, identifying these **five coefficients of a posited linear model** (not separating every conceivable confound). A nominal active/sham design with one dipole orientation has rank **2**, and repeating its arms does not improve rank. The code requires measured settings and documents `actual_coil_current_measured=False` and `dipole_polarity_experimentally_verified=False` until genuine instrument receipts are inspected. Measured gradients still enter ordinary-force prediction directly; polarity rank does not validate the fixed-dipole law or prove gravity effects.

### S6 stable singular values

[Updated S6 static response owner](../../scripts/psychotronics_field_loom_observability.py) computes the **smaller** singular value using the two-column Cauchy–Binet identity:

```text
σ_min = sqrt( Σ_(i<j) (a_i b_j - a_j b_i)² ) / σ_max
```

This avoids subtractive cancellation at near rank one and provides exact-zero minors for mathematically collinear columns. Adversarial collinear, zero and perturbed matrices are included in the regression source, alongside the prior ideal two-coil 9/27/81-observation rank test and exhaustive `27 choose 4 = 17,550` single-sensor-failure layout search. The four-sensor optimum is **under the stated ideal geometry and equal-noise/maximin objective only**.

## Test strategy and status

[Unified offline regression suite](../../scripts/test_psychotronics_field_loom_gate.py) covers numerical Biot–Savart vs closed form, group-shared uncertainty not averaging away, independently calibrated group conditional contrast, factorial rank with duplicate rows, S6 zero/rank-one/fault case, same-object hash source and tamper rejection, and synthetic-result promotion refusal. Each corresponding module also contains its own synthetic `_selftest` where applicable.

**Verification boundary of this update:** the GitHub connector accepted the source changes; independent local algebra checks were carried out in the model's Python runtime. **No checked-out GitHub Python blobs were executed in that runtime** because the container cannot resolve github.com; the committed tests are ready to run offline on an existing repository checkout, but must not be reported as having passed on GitHub or CI. Agda typechecking/CI and any physical force, external gravity, safety or clinical experiment were **not performed**.

## Pareto consequences and stopping rule

**Paid:** source-written code for an explicitly correlated uncertainty estimator, structurally bound submitted pairs/calibration/stream receipts, exact polarity-design identifiability, cancellation-resistant S6 rank calculation, unified regression test source, and the documentary/instrument requirements linking S1 to the pre-existing Amy/antigravity observation/provenance owners.

**Not paid:** authenticated physical measurements; independently verified raw-stream→pair reducer; verified instrument calibration/timebase and covariances; complete systematic-error budget with thermal/vibration/EHD/mechanical backgrounds; a source-specific gravitational observation channel; physical force residuals and independent replication. The actual next information gain comes from **real instrument acquisition/calibration and reproducible paired datasets**, *not* more purely synthetic mathematics. Historical H source acquisition remains separate, including the 1973 Pavlita/Jana original and 1975 primary apparatus pages when actually accessible; the 20-scientist technical fibre ledger must not be reinterpreted as event or perpetration attribution.

**Proposed phase revision:** S1 design/inference **advanced, but physically unvalidated**; S6 ideal/fault design advanced, **no hardware**; G physical anomaly still **none accepted**; I existing scientifically attributed fibres now linked to practical methods, not a joined secret programme. Next change in phase requires an actual calibrated source object that survives conventional-force controls and is accepted in the relevant evidence consumer, not a boolean review flag.
