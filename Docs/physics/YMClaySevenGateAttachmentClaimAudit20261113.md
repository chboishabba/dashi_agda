# Yang–Mills seven-gate attachment: exact source and mathematical validity audit

**Date:** 13 November 2026. **Owner:** Agda [#1444](https://github.com/chboishabba/dashi_agda/pull/1444). **Related perturbative owner:** Agda [#1498](https://github.com/chboishabba/dashi_agda/pull/1498). **Source:** user-supplied `Pasted text.txt`, 204 lines, beginning with the original F19 identity and concluding with a proposed `YMClayP0ScalarTraceWeldExact`. The attachment's "constructively closed" labels for all seven physical Clay gates must **NOT** be used as proof receipts.

## New exact progress already present (do not redo)

1. Actual original original `YMClayOriginalWilsonPhysicalF19PartitionExact.originalFinePhysicalPartitionEqualsActualEffectivePartition`: original 1024-link interacting Wilson partition equals the physically constructed 64-pair/896-spectator fine-to-effective partition, with all couplings.
2. Actual original `YMClayOriginalWilsonPhysicalF19PartitionExact`: source-written positive Gibbs/spectator/effective/fine partition and original canonical two-source `Z_aff(0,0)=Z_original` positive normalizer (kernel pending).
3. **Important newer source owner:** `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective` already proves a full normalized original canonical Wilson **blocked-holonomy observable** -> actual F19 effective-source expectation for any 64-block coarse test. Original 1024-bond permutation, same measure, original 64 pair holonomies, full 896 spectators. This substantially pays P0.E; the original Wilson-loop word family / reflection and two-jet semantic identifications are the remaining source steps.
4. `YMClayOriginalPlaquetteTraceCyclicityInsufficientExact` already proves in the *legacy real carrier* that constant-valued cyclic traces force any alleged generic trace bound to bound **every** scalar. New `YMClaySUNTraceCyclicityDoesNotImplyRangeExact` constructs the exact source `SUNMatrixRealTrace` with **Nat-valued constant two**, and refutes the attempted universal Nat-unit-range theorem using the actual `SUN.sunIdentity`. This is only a semantic negative control; it does **not** refute the genuine real SU(N) normalized matrix trace bound.

## Eight exact claims audited from the attachment

### P0 Scalar — positive finite Wilson Gibbs Z, but **Bishop apartness remains open**

The attachment uses `Z>0 ⇒ Bishop apartness` without inhabiting `OriginalWilsonToBishopScalarWeld`. The positive `Z` theorem lives in the legacy **postulated** `RealAnalysisAxioms.ℝ`, whereas the reciprocal/apartness constructor works on the independent constructive Bishop `Real.ℝ` setoid. The faithful operation/order-preserving interpretation (and its equality reflection) is not provided by a sign proof alone. `LegacyDASHIRealEquivalenceAuthorityExact` is another explicit uninhabited authority, not a bridge inhabitant.

The lower bound `exp(-beta*P)` is generally **a positive real, not a positive rational**. A rational Bishop apartness modulus requires source-certified rational underapproximation and representation agreement. The attachment also changes the action convention: `beta/(2N) ReTr(I-U)` has per-plaquette max `beta` at `U=-I` for beta≥0, while the current `periodicSUNWilsonAction` is `beta * Σ(1-normalizedRealTrace U)`, whose per-plaquette max may be `2beta` when the *true* trace is ReTr(U)/N. The source trace record need not even have this range until P0.Trace is paid. A uniform positive Z lower bound must choose and prove the **actual** action normalization, beta sign and physical Haar measure.

**Status:** native finite positive Z source-written; original-Bishop scalar interpretation OPEN.

### P0 Trace — true standard lemma, wrong currently selected carrier

For a **genuine** unitary complex N×N matrix with N≥1, orthonormal columns, Cauchy–Schwarz and triangle inequality give `|Re Tr(U)/N|≤1`. But the original `SUN.CertifiedSUNMatrixTheory` provides abstract Matrix multiplication, dagger, determinant and group laws, **not indexed complex entries, diagonal trace sum, vector norms, or Cauchy–Schwarz**. `SUNMatrixRealTrace` provides only an arbitrary scalar map plus cyclicity. Its `normalizedRealTrace` is not definitionally the true normalized matrix trace. The attachment assumes the missing matrix-normalization authority rather than implementing it.

**Status:** standard external mathematics available; native arbitrary-N source theorem/weld OPEN.

### P0.F — running coupling is neither an actual Wilson moment estimate nor summable

The attachment writes `g0²(a_k)=constant/(k ln 2+c)` and promotes this to an **original nonperturbative effective-minus-bare** Wilson moment estimate. Existing CMP109 beta extraction is a conditional perturbative mixed off-diagonal two-jet, not a nonperturbative theorem controlling the real-space full Wilson effective action, large-field tails, and volume uniformity.

Even assuming `ε_H(k)≤C_H/k`, **Σ_k (1/k) diverges**. The fixed ratio `a_k/L_k=1/4` contributes a constant `1/16`, not a geometric per-scale decay. `C_H`, Green-function diagonal, background covariance, quartic/higher jets and large-field suppression are not proven uniform for the original physical Wilson measure. Gaussian odd-moment cancellation is not automatic for its coupled non-Gaussian background measure. The selected `g0²` beta convention also needs matching to the actual one-loop (b_0) definition.

The ACTUAL owner `YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact` already proves the covariance telescope **conditional on three ORIGINAL physical moment-error bounds**, and `YMClayOriginalWilsonPartitionEqualityDoesNotBoundRGExact` plus `YMClayP0FGeneratedTwoSourceInteractionNegativeControlExact` already show exact partition equality/marked pushforward cannot force those errors small. These counterexamples do not refute a future true physical RG bound.

**Status:** three original physical error estimates with UV+volume-uniform, sufficiently summable/cancellation-controlled behavior OPEN.

### E1 — passing to a sparse geometric subsequence cannot close full cutoff convergence

The existing exact rational `scripts/check_ym_e1_harmonic_regrouping_countermodel.py`, **now strengthened**, checks 131071 adjacent `|s_{k+1}-s_k|≤2/k` estimates for a bounded, non-Cauchy sawtooth. Stronger still:
`s_{4^j}=0` for all j (an **exactly convergent geometric subsequence**), while `s_{2·4^j}=1`. Thus even perfect convergence on one sparsified UV scale sequence does not force full cutoffs to converge; every dyadic block has `Σ_{k=2^j}^{2^{j+1}-1} 1/k≥1/2`. The attachment's `2^{-δj}` comparison is not derived from the proposed `1/k` adjacent error. Additional tightness, reflection positivity and projective consistency are needed to construct the *requested* continuum Radon probability measure on the correct distribution/gauge quotient, rather than only a pointwise cylinder functional.

**Status:** interacting continuum E1 OPEN.

### D1 — the input polymer-activity bound is the missing mathematics

Given a valid uniform original lattice activity estimate `|ρ(X)|≤C e^{-m_1|X|}`, a correct polymer counting theorem and `m_1>log(entropy base)`, a geometric tail is elementary. The attachment simply asserts `m_1(k)≥log64+2` without a proof from the **interacting original Wilson** small/large-field RG. The proposed `64^n` rooted-polymer bound is not a sourced original connected-cluster count. A gap of `(m_1-log64)/L_k` additionally requires uniform **physical** length scaling; as `L_k→∞`, a fixed block-count exponent would yield zero physical rate.

**Status:** original uniform connected-polymer activity estimate and physical-time scaling D1 OPEN.

### D2 — correct conditional spectral logic, but physical rate/core unresolved

For a nonnegative self-adjoint H on a genuine reflection-positive OS Hilbert space, a **common** exponential time exponent m>0 for a dense vacuum-orthogonal domain can imply a full-sector spectral gap (provided the semigroup/core/source hypotheses are correctly met). This standard spectral implication is already the subject of the original R581–R583 same-H/dense-core architecture. What the attachment treats as constructed is the **continuum** OS H, the source identification of its vacuum-orthogonal dense genuine Wilson test core, and a common source-proven m>0 on that core; an isolated selected autocorrelation or finite-lattice RP test does not provide them. A separate dense-core spanning *assertion* is not a proof of physical density.

**Status:** same-H continuum full nonvacuum spectral gap D2 OPEN.

### N1 — leading connected four-point formula is not an evaluated physical witness

The attachment asserts an unverified quartic-looking expression `-g_ren^4∫∏G_cont + O(g_ren^6)` for a gauge-field-strength connected 4-point, with an unquantified remainder and positivity of scalar propagators. The actual field-strength product and source gauge invariance, connected cumulant, nonzero tensor/color coefficient, renormalized normalization and remainder **uniformly smaller than its leading term** must be paid; the expression is not derived by the finite F19 partition theorem. Even for an asymptotic series, a nonzero displayed leading coefficient does not prove `|G4|≥c g_ren^4` at selected finite coupling without a certified bound on the omitted terms.

**Status:** interacting continuum N1 OPEN.

### G1 — dual Coxeter positivity does not imply nonperturbative universal gap

Dual Coxeter numbers are positive for compact simple Lie algebras and determine a **perturbative** universal coefficient in the conventional normalization, but the attachment gives no source-specific E1 construction, uniform polymer D1 estimates, D2 physical Hilbert/spectrum, N1 witness or checked original group carrier for all simple groups. Normalization and low-rank group conventions matter; the original group coverage is more than a type-level `h^∨(G)>0` fact.

**Status:** G1 OPEN.

## Separate Bałaban physical 12-gate route (#1498)

Do not conflate the full finite 1024-link physical F19 pushforward with Bałaban's **perturbative** four-diagram Fourier/Ward/one-loop beta scalar. The latest #1498 has original denominator-topology AST and indexed four-sector tensor Ward syntax, free rational Feynman-gauge propagator inverse, reduced ghost fifth tail, real rational midpoint Hessian coefficient `1/384` on the x-box and `1/6144` on the physical normalized cell, and a four-orbit combined error-budget compiler. It is STILL missing the actual P33 Wilson cubic/quartic indexed Fourier numerators, background FP/Haar physical source and semantic Ward cancellation, shifted sine denominator positivity, true source quadrature integral/Hessian estimates and the correct beta coefficient/remainder. The attachment does not solve any of those 12 terminal P0 gates.

The numeric identity `4*(7071/10000)^2=199996164/100000000=1.99996164` is correct, but an enclosure of the actual sine atom and source physical denominator remains a separate gate.

## Exact acceptance checklist / trust

- [x] Original canonical F19 interacting full partition / marked blocked pushforward: source-written **on #1444**.
- [x] Original 1024-link positive F19 partition and two-source Z: source-written **on #1444**.
- [x] Existing real-scalar cyclicity warning + new explicit Nat constant-two original source negative control: source-written, **kernel pending**.
- [x] Exact-rational full-E1 non-Cauchy and convergent sparse-subsequence control: independent Python executed, **131071 bounds PASS**.
- [ ] Local pinned Agda 2.9 kernel receipt on exact #1444 head: **NOT available**.
- [ ] Faithful Bishop ↔ original-real source interpretation and native normalized complex trace: **OPEN**.
- [ ] Original physical three (F,G,FG) errors with uniform summable RG control: **OPEN**.
- [ ] Actual continuum E1, connected-polymer D1, same-H D2, interacting N1, all-group G1: **OPEN**.

**No change in Clay status; no original physical estimate is promoted from a formal diagram, theorem consumer or perturbative analogy.**
