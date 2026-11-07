# Roadmap: DASHI Agda Closure

## Overview

Stabilize the empirical geometry layer (Fejér/prox/MDL/cone with snap exceptions), then sweep remaining postulates and formalize signature elimination and closure harness wiring.

## Domain Expertise

None

## Phases

- [ ] **Phase 1: Geometry Seam Hardening** - snap signatures, cone interior predicates, Lyapunov wiring.
- [ ] **Phase 2: Postulate Sweep** - replace remaining low‑risk postulates with constructive proofs.
- [ ] **Phase 3: MDL Integration** - make Lyapunov/MDL claims explicit across closure layers.
- [ ] **Phase 4: Signature Elimination** - encode orbit‑profile discriminator and masked‑Q elimination seam.
- [ ] **Phase 5: Closure Harness** - consolidate empirical→full wiring and documentation.

## Phase Details

### Phase 1: Geometry Seam Hardening
**Goal**: Formal snap exception class + cone interior predicate + Lyapunov witness wiring.
**Depends on**: None
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [x] 01-01: Define snap signature instance and cone interior predicate for shift.
- [x] 01-02: Wire cone‑monotone‑except‑snaps to shift operator.

### Phase 2: Postulate Sweep
**Goal**: Remove remaining low‑risk postulates (e.g., periodicity, simple order properties).
**Depends on**: Phase 1
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [x] 02-01: Scan for postulates in numeric/finite modules; replace with stdlib lemmas.
- [x] 02-02: Validate compile of affected modules.

### Phase 3: MDL Integration
**Goal**: Make MDL Lyapunov/Fejér concrete in closure adapters.
**Depends on**: Phase 1
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [ ] 03-01: Provide MDL Lyapunov witness in empirical→full adapter.
- [x] 03-02: Add beta‑space seam instance or hook to CSV evidence.

### Phase 4: Signature Elimination
**Goal**: Encode masked‑Q rank / orbit‑profile discriminator as signature lock seam.
**Depends on**: Phase 1, 3
**Research**: Likely (mapping empirical evidence to Agda predicates)
**Research topics**: Masked‑Q screening assumptions, orbit‑profile fingerprint constraints
**Plans**: 2 plans

Plans:
- [x] 04-01: Define `SignatureLock` instance shape + eliminator lemma skeleton.
- [x] 04-02: Wire empirical mask ranking into signature lock stub.

### Phase 5: Closure Harness
**Goal**: Consolidate wiring and update project docs.
**Depends on**: Phase 2–4
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [ ] 05-01: Merge empirical harness with full closure pack.
- [ ] 05-02: Update `.planning/CONTEXT.md` and `.planning/COMPACTIFIED_CONTEXT.md`.

## Progress

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. Geometry Seam Hardening | 2/2 | Complete | 2026-02-28 |
| 2. Postulate Sweep | 2/2 | Complete | 2026-02-28 |
| 3. MDL Integration | 1/2 | In progress | - |
| 4. Signature Elimination | 2/2 | Complete | 2026-03-01 |
| 5. Closure Harness | 0/2 | Not started | - |


## Cross-domain geometry lane: Gielis × Base369 (November 2026)

**Authority:** [GielisBase369Roadmap.md](../Docs/support/reference/GielisBase369Roadmap.md).
**Implementation:** [PR #1466](https://github.com/chboishabba/dashi_agda/pull/1466), draft;
the original closure phases above remain unchanged.

- [x] Phase G0: prior-art owner mapping (dihedral, Nyquist/Shannon, MDL/Kolmogorov, SO(3)/torque, log-polar spiral).
- [ ] Phase G1: G01/G06 native C18 and 36-sector exact proofs **kernel-accepted**; three new sources present but compiler receipt outstanding.
- [ ] Phase G2: G02–G05/G08–G09 ordinary-real Gielis identity, cyclic/dihedral continuum, area/curvature.
- [ ] Phase G3: G07/G10–G12/G19 native Fourier, sampling and convergent Dirichlet spectrum.
- [ ] Phase G4: G13–G16/G21 original Kozyrev HTML raymarcher same-apparatus reproduction, calibrated angular impulse, non-369 controls, CI and Pareto.
- [ ] Phase G5: G17/G18/G20 inverse/MDL/product-symmetry proofs, reproducible paper and independent physical validation.

**Deliverables:** D0 prior-art map; D1 kernel receipt; D2 continuous geometric
library; D3 spectral certification; D4 source/geometry parity; D5
control/Pareto benchmark; D6 empirical validation; D7 inverse compiler and
publication. The exact G01–G21 lemma list, dependencies, owners, tests and
nonpromotion rules live exclusively in the linked lane roadmap.

### Gielis round-2 mathematical certificates, separate from Golden acceptance

- [x] Paper-level exact special-case Gielis identity, smooth star boundary,
  3/6/9 dihedral symmetry, and common area `sqrt(2)*pi` (E01–E03).
- [x] Paper-level normal/curvature formulas and 3/6/9 nonconvexity (E04).
- [x] Full finite cyclic-group projector identity and exact selected 36-sample
  bandlimited reconstruction, with 18-sample aliasing counterexample (E05–E06).
- [x] Standard-theorem argument for Dirichlet compact resolvent and disk/Faber–Krahn
  first-eigenvalue bounds; **not** a mesh-error proof (E07).
- [x] Correct wall-versus-ray impulse sign and derive conditional optical
  power-to-SI-torque conversion; no measured power claim (E08).
- [x] Explicit zero-modulation inverse-identifiability counterexample and
  C27 versus C3^3 nonisomorphism; computational prefix code (E10–E11).
- [ ] G01–G05/G07/G08/G09/G10/G11/G19: **ordinary-real Agda kernel**
  certificates for the paper mathematics and finite carrier transport.
- [ ] G12: rigorous numerical PDE eigenvalue discretization convergence/errors.
- [ ] G13–G16/G21: original HTML Kozyrev mirror source/collision parity,
  committed-head executable receipt, optical power calibration and CIs.
- [ ] P5: independent physical measurements and replication.

See [Proof theorems](../Docs/support/reference/GielisBase369ProofTheorems.md)
for E01–E11 and [exact gate roadmap](../Docs/support/reference/GielisBase369Roadmap.md)
for G01–G21, status, phases, dependencies and D0–D7.


## Gielis × Base369 round-four proof/implementation delta (November 6, 2026)

- [x] E12 source-written universal Bishop polynomial normal form, using real project's solver. Actual Bishop Pythagorean, quadruple-angle, pi and sqrt integration and Agda --safe checks remain [ ].
- [x] E13 exact cyclotomic Q(zeta36) character orthogonality: 1296 pairs and exact selected seven-mode inversion (local executable check passed). Agda native Fourier instantiation remains [ ].
- [x] E14 continuum angular-sector domain spectral O(m/N) bound for all Dirichlet eigenvalues; exact rational m=9, N=2048 error less than 1%. Cartesian finite-difference numerical error certification remains [ ].
- [x] E15 first-eigenvalue Rayleigh bound for the m=3 Gielis domain: lambda1 < 1273/264, verified via symbolic integral and rational arithmetic. Native Bishop Hilbert formalisation remains [ ].
- [x] E16 independent new-scene 80-ray continuous-root versus polygon ray first-hit convergence: max error 0.223 mm (384 seg) versus 0.0125 mm (1536 seg). Original HTML SDF same-apparatus parity remains [ ].
- [x] Source-code implementation of IID uniform-angle Hoeffding simultaneous intervals for focus/impulse. Physical source probability/measurement/replication remains [ ].
- [x] Independent local math regression set, 7 tests PASS. NOT the exact-head GitHub Agda+pytest receipt.
- [ ] G01 Agda --safe for all four native sources, including the Bishop polynomial module.
- [ ] G02–G05/G08/G09 actual Bishop ordinary trigonometric/square-root/pi continuous proofs and kernel acceptance.
- [ ] G07/G10/G19 actual C36 cyclotomic Fourier Agda module and exact resolution owner instance.
- [ ] G11 native Dirichlet operator/Hilbert formalisation; G12 verified Cartesian FD solver error.
- [ ] G13/G14 original Kozyrev HTML SDF source scene/collision parity.
- [ ] G15/G16 measured optical power, wall reflectivity, physical torque/uncertainty and actual Pareto validation.

Authoritative proof details: Docs/support/reference/GielisBase369ProofTheorems.md (E01–E16). Exact phase/deliverables/status: Docs/support/reference/GielisBase369Roadmap.md (P0–P5, D0–D7, G01–G21).
 
### PR #1466 — Gielis max-cut update: canonical Kozyrev and certified discrete spectrum

- [x] E17: rigorous Perron–Frobenius exact-rational first eigenvalue intervals for original raster FD 41x41 (m=3,6,9) and 61x61 (m=3). Original finite matrix eigenvalue error is certified independently of eigsh; **FD-to-continuum convergence remains OPEN G12b**.
- [x] E18: Original Kozyrev implementation is **PR #1404** (head 337aabb), not an unknown repository. Exact epsilon-zero Gielis/log-spiral centreline identity. SHA-pinned adapter to original Kozyrev first-forward referee + RayLedger built.
- [ ] E18 acceptance: run source-pinned normal-offset wall first-hit parity (G13b); separate original browser HTML SDF collisions and recorded event files G13c remain OPEN.
- [x] E19: exact conditional P,R,eta,B radiation-pressure optical torque envelope, plus paired uniform-angle source Hoeffding contrast model. This is NOT independently measured apparatus torque/CI.
- [ ] G02–G05/G08–G09: actual Bishop sin/cos same-object weld, double/quadruple-angle, pi, real inverse/sqrt and Agda Golden still OPEN. A native universal Bishop-real fourth-degree algebraic reduction now exists in source.
- [ ] G07/G10/G19: Python Q(zeta36) 1296-pair exact results need native Agda character and reconstruction owner.
- [ ] G15/G16: original apparatus measured power, reflectivity, mechanical torque, full controls, uncertainty and independent replication.
- [ ] G21: exact-head parallel checker acceptance and PR #1404 cross-ref events and signed torque parity.

Proof explanations E01–E19: Docs/support/reference/GielisBase369ProofTheorems.md.
Authoritative G01–G21 obligations and deliverables: Docs/support/reference/GielisBase369Roadmap.md.


## 2026-11-06 Gielis: existing SI + Perron formal-owner reuse (active max-cut)

- [x] Reuse canonical SI seven-exponent Dimension/Quantity/Measurement in `DASHI.Physics.Units.SI` and `SIMetrologyBridge`; no second physical-unit system.
- [x] Reuse Buckingham M/L/T algebra and existing mechanical→SI mapping; source-write the exact `[P/c]R = M L² T⁻²` dimensional theorem.
- [x] Preserve nominal meaning of wall torque (N m) and optical energy (J) as distinct roles despite equal dimensional exponents; angular impulse has M L² T⁻¹.
- [x] Reuse canonical SI exact c natural-number carrier `SIExactConstantParsedCarrierRequest` (299792458 m/s); Python optics/torque now reads that canonical source.
- [x] Reuse actual Yang–Mills/Balaban finite **nonnegative rational matrix row/power** theorem in `GielisSIPerronOwnerWeldExact.agda`, avoiding a duplicate Perron library.
- [x] Keep E17 original finite-raster Collatz–Wielandt rational eigenvalue interval, verified mathematically; do not confuse Syracuse integer dynamics with the Perron variational theorem.
- [ ] The five new Gielis Agda roots require exact-head kernel acceptance; the universal Gielis Bishop trigonometric weld and native selected raster spectral owner are still distinct obligations.
- [ ] Cross-calibrate actual optical power/reflectivity/lever-arm measurements to typed SI quantities if a physical empirical endpoint is required.

**Scope adjustment:** CI and historical HTML ray replay are deferred from the active priority cut, not erased from the G13 provenance ledger. Full E01–E21 proof details and G01–G21 remaining exact lemmas: `Docs/support/reference/GielisBase369ProofTheorems.md` and `GielisBase369Roadmap.md`.


## Gielis max-cut native theorem transport: E22–E26 (Nov 6, 2026)

- [x] E22: actual quantity-level rational `Mechanical.multiplyQuantity` for `((P*c^-1)*R)*g`, SIIndexedQuantity transport, and explicit distinction of signed geometric response g from measured power.
- [x] E23: source-written native inverse-area Laplace eigenvalue unit transport and fully rational CONTINUUM m3 length-scaled envelope (9/(4 Lmax²) < λ₁ < 1273/(264 Lmin²)); no wave frequency inferred.
- [x] E24: exact rational assumed-input intervals for power, hit radius and reflectivity; `|τ|≤(Pmax Rmax/c)(1+ηmax)Σ ηmax^k`; zero lower bound and no false measured CI.
- [x] E25: native Bishop setoid/ring derivation of `4(cos_B⁴+sin_B⁴)≃3+cos_B(4x)` from ACTUAL configured sine/cosine Pythagorean and quadruple-angle inputs; the analytic same-object producers and kernel check remain [ ].
- [x] E26: native rational ring/sum/positivity proof of arbitrary finite weighted-graph edge correction; exact ground-state identity supplies first finite raster eigenvalue lower bound without PF/connectivity assumption. Independent exact-fraction check 120 graph/vector pairs PASS.
- [ ] Golden acceptance: true Round11 Bishop trigonometric quadrupling/weld; C36 cyclotomic reconstruction; actual Gielis raster vertex aggregate; Cartesian FD-to-continuum; selected SI optics actual collision/source magnitude; Agda kernel acceptance of seven roots.

No parallel CI or original HTML replay pursued, per current user scope.
Canonical E01–E26 proof note: Docs/support/reference/GielisBase369ProofTheorems.md.
Canonical G01–G21 exact remaining lemmas: Docs/support/reference/GielisBase369Roadmap.md.


## 2026-11-06 E27 original raster continuum proof and exact target repair

- [x] Discover and repair original raster FD radial boundary FIXED-epsilon asymptotic wrong-target defect: replace 1e-12 by δ(h)=min(1e-12,h²), retaining identical n41/n61 masks.
- [x] Exact original zero-extended 5-point energy identity u^T(4I-B)u = Σ_edges(u_i-u_j)²; implemented exact integer/Fraction checker with four independent selected vectors.
- [x] Qualitative mathematical fixed-k Cartesian FD spectral convergence for the exact analytic domain under corrected vanishing ε: smooth-test limsup, compactness/liminf, zero exterior trace, min-max.
- [ ] Controlled literal binary64 boundary evaluation / interval-certified actual finite mesh parity for arbitrary small h (fixed roundoff cannot be treated as o(1)).
- [ ] Quantitative continuum n41/n61 eigenvalue error bound and native Agda continuum compactness/raster proofs.
- [ ] Actual Bishop Round11 trigonometric object, C36 Fourier scalar and original SI optical source transfer physical semantic weld.

The existing YM Mosco recovery/liminf owners are status inventories, not Gielis theorems. The full proof E27 and exact G12/G21 gate updates are in the existing canonical Gielis proof notebook and roadmap. CI/HTML are not active priorities.


## 2026-11-07 Gielis decisive native/analytic tranche E28–E35

- [x] E28: original Phase36 quarter-wave m9 rational Fourier, both native source-written inversions, exact Q(zeta36) interoperability (625 exact round trips).
- [x] E29/E33: actual Round11 Bishop cosine/sine quadrupling reduced to ONE selected imaginary-axis complex exponential multiplication law; original Bishop real expAdd and trig setoid congruence reused.
- [x] E30: native C6=C2×C3 selected phase Fourier, full two-sided inversion using existing C3CubeCyclotomicFourierExact; 729 exact cyclotomic sample/direct-DFT comparisons.
- [x] E31: EXACT rational unshrunken integer-mode Gielis raster membership in original FD solver, eigenvalue referee and discrete energy script. Four legacy selected masks unchanged: 792/779/792/1788, zero classification mismatches; fixed binary64 boundary error removed from actual algorithm.
- [x] E32: native signed original radiation-pressure angular lever `x*(in_y-eta*out_y)-y*(in_x-eta*out_x)`, typed SI N m value with nominal torque vs energy role and exact rational event tests.
- [x] E34: same ORIGINAL Bishop complex algebra source now has native associative/commutative multiplication and distributivity proof terms, reusing existing real ring solver.
- [x] E35: all-positive-integer-m mode continuum Dirichlet first eigenvalue LOWER `lambda1>224/55` from exact area sqrt(2)pi, Faber-Krahn and rational Bessel alternating bounds. Source-written native rational S5=608149/244140625, sqrt2 upper and scalar bound; SI physical scale consumer improved.
- [ ] G-BISHOP: complete actual Bishop *complex* factorial Cauchy coefficient/limit and imaginary-axis sine/cosine identification; original Round11 Pythagorean same-object weld, pi, sqrt, radial derivatives/polar integration.
- [ ] G-FOURIER36: native full 12D Q(zeta36) scalar and generic 36-mode resolution/inversion; selected C4/C6 are closed subcases only.
- [ ] G-SPECTRAL: fully native raster operator/compactness/continuum min-max and quantitative finite-grid spectral error; exact membership + finite rational eigen brackets and paper convergence already paid.
- [ ] G-SI-PHYSICAL: measured original source power/reflectivity/directions/impact coordinates/uncertainty, with physical evidence and replication if claims are empirical.
- [ ] GOLDEN: Agda kernel acceptance of the 14 registered Gielis roots on the actual repository parallel checker. Source-written is not equivalent to typechecked.

Current canonical docs: `Docs/support/reference/GielisBase369ProofTheorems.md` (E01–E35),
`Docs/support/reference/GielisBase369Roadmap.md` (G01–G21; P0–P5; D0–D7).
Per user request, CI chasing and historical HTML replay are not current active gates.


## 2026-11-07 verified Gielis missing-lemmas correction (E36 owner archaeology)

Prior priority labels P0–P3 were too coarse: SOURCE-VERIFIED original owners are present and must be consumed, not reimplemented.

- [x] P0: `BishopComplexSeriesConvergenceExact` proves componentwise complex series limit/convergence/uniqueness; `BishopComplexAlgebraExact` supplies complex arithmetic/powers; `BishopSetoidComplexExact` supplies expC and congruence (two structurally related but distinct Agda record carriers).
- [x] P0: `BishopExponentialFiniteCauchyCoefficientExact` and `BishopExponentialCauchyProductExact.bishopExpAdd` already construct factorial convolution and real analytic exponential multiplication.
- [x] P0: `BishopMachinPiRationalWindowExact` has 3 < π_M < 22/7, `BishopNatSquareRootSemanticSquareExact` proves the constructed sqrt(N) semantic square for natural N, `BishopPolarJacobianSameTrigWeldCompilerExact` already owns selected trig derivative/pointwise polar determinant.
- [ ] P0 actual consumer leaf: selected complex exp factorial Cauchy + Round11 cosine/sine same-object weld, Machin π trigonometric period identity, variable positive root/reciprocal, Gielis-specific polar integration. Polar measure owner explicitly has `measureTheoreticWeldClosed=false`.
- [x] P1: `ShorCyclicCharacterResolutionExact`, `ShorCyclicDFTLeanCrossProverWeldExact`, `NSTriadKNLuoFiniteFourierInversionFromResolutionExact`, Parseval and native C3³ scalar Fourier already exist.
- [ ] P1 specific leaf: choose original Q(zeta36) 12D coefficients and exhibit all 36 root character resolution laws / same Fin Q normalization.
- [x] P2: finite Hermitian/Rayleigh and Mosco/recovery/spectral interfaces exist; Gielis exact finite geometry/energy and paper fixed-mode convergence already supplied.
- [ ] P2 specific leaf: native selected Gielis forms/density/minmax and quantitative n41/n61 continuum error. Original YM Mosco interfaces are partly conditional/fail-closed.
- [x] P3: Kozyrev original PR #1404 `scripts/kozyrev_optical_event_ledger.py` implements P/c ray force, r×impulse torque, reflectivity/absorption, along with log-spiral optimizer and first-forward intersection referee.
- [ ] P3 specific leaf: selected Gielis event to SAME Kozyrev RayLedger and actual measured apparatus inputs/uncertainty if empirical claims are made.
- [ ] Agda native Golden receipt outstanding; CI and HTML excluded from active priority by user direction.

See `Docs/support/reference/GielisBase369ProofTheorems.md` E36 and `GielisBase369Roadmap.md` corrected G02/G03/G04/G08/G09/G10/G11/G12/G15/G16/G19/G21.
