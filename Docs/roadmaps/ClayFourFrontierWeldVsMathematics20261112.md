# Four Clay frontiers: source-corrected max-cut and weld-vs-mathematics ledger

**Date:** 12 November 2026. **Authority:** original source definitions, locally pinned Agda (golden) and Lean (cross-kernel donor) receipts. **Input:** attached `Pasted text.txt` four-frontier architecture. **Status:** audit and exact regression executed; newly authored Agda source is **not kernel accepted** until the pinned local checker runs. No Clay endpoint is declared solved here.

## Corrected declarations and what the attachment did NOT prove

### Navier–Stokes (periodic B vs external R³ C/D)

1. **Periodic cell flux:** the boundary integrals from *opposite fundamental-domain faces* cancel under appropriately periodic fields and traces. This says nothing about the flux through an arbitrary artificial interior cutoff surface, nor about the R736 **remote boundary/collar source** without its exact domain and integrand. **Paid mathematics:** global-face pairing. **Unpaid mathematics:** R736 actual selected cutoff flux estimate and smooth-localisation boundary cancellation. Do not rewrite one as the other.
2. **Collar/Young obstruction:** the proposed `delta^(1/4) A^(1/2) B^(5/2)` bound cannot be absorbed into `nu/2 * B^2 + C_nu delta^(3/2) A^6` by Young. The exponent `5/2 > 2`; the suggested `(6/5,6)` exponent would produce `B^3`, not `B^2`. For `delta=A=nu=1`, `B=n^2`, the left is `n^5` and the right `n^4/2 + C`, contradicted for large `n`. **Unpaid mathematics:** a *genuinely absorbable* selected original signed collar inequality or other new control on stretching/concentration.
3. **Energy vs enstrophy continuation:** `int_0^T ||grad u||_2^2 < infinity` does not bound `int_0^T ||grad u||_2^3` or any uniform-in-time enstrophy; e.g. `A(t)=t^(-3/4)` is integrable but `A^(3/2)` is not. R829 instantaneous rate is **not** an integrated global trajectory. BKM concerns `int ||omega||_infty dt`, not the statement attributed to it in the attachment. **Unpaid mathematics:** selected physical real-time reserve, finite ODE transport and continuation argument.
4. **Actual LeanDojo C/D exact five leaves** (confirmed directly in `ExternalClayNS/LeanDojoCComparatorBridge.lean` of Lean #51): `ClayInitialDecayToLeanDojo`, `ClayForceToLeanDojo`, `LeanDojoMomentumToClay`, `LeanDojoIncompressibleToClay`, `LeanDojoEnergyToClay`. These concern **R³ smooth initial/force fields, positive-time equations, closed-half-space boundary, vector norm**, NOT the periodic T³ weak Leray–Hopf lemmas in the attachment. **Category:** representation + analytic boundary-extension welds; not new fluid estimates if original exact comparators and smoothness hold. No completion until exact pinned target term and axiom audit.

### Riemann Hypothesis (G3 / A1 / A2 / B)

5. **Signed-fifth counterexample:** for an even real `C^1` rapidly decaying `H`, with vanishing boundary term, the attachment's literal functional obeys `int x^3 H² = 0` and `int x^5 H'H = -(5/2) int x^4 H²`, hence `Delta5 = -(5/2) int x^4 H² < 0` for nonzero `H`. Exact rational polynomial negative control: `H(x)=(1-x²)²` for `|x|<=1`, `0` otherwise. Then `int x^4 H²=256/15015`, `Delta5=-128/3003`. This refutes the **attachment's formula**, not DASHI's distinct `signedFifthCorrelationGapAt`. **Unpaid mathematics:** the latter original Route-B signed-fifth eventual nonnegative gap, if valid; proof must use that exact definition and any required physical cap.
6. **Curvature/shell error:** the displayed positive shell sum assumes an unproved distribution and uses `sigma-1/2` for all zeros even when an off-line zero is the contradiction hypothesis. Pointwise positivity of `partial_sigma² log|xi|` does not follow from the Hadamard product or `log t` without a complete signed, uniform, source-specific estimate. Avoid evaluating `log|xi|` at a zero. **Unpaid mathematics:** A2 original strict lower-order/far compensation inequality; A1 actual shell-assignment, uniform curvature and gain/slack; G3 strict signed residual scalar. Existing conditional compilers remain only conditional.
7. **Flow:** evenness is insufficient to make `H'(x) H(x)` sign-definite; heat-semigroup direction/normalisation and de Bruijn–Newman implications must use the original source. No conclusion `Lambda<=0` or RH follows from the proposed `Delta5`.

### P versus NP (direct SAT vs Karp-21)

8. **Quantifier correction:** the attachment asks for `exists phi, forall polynomial D, D(phi) != SAT(phi)`. In any standard cost model certifying both constant Boolean algorithms, for every selected `phi` one constant algorithm agrees at `phi`. This is source-written in new native module `PNotEqualsNPFixedInstanceQuantifierNoGoExact.agda` against the original `PolynomialSATDeciderCandidate` and `PolynomialCostModel`; the actual needed shape is `forall polynomial D, exists phi, D(phi) != SAT(phi)`. **Unpaid mathematics:** universal SAT lower bound, without assuming an impossible short self-referential tableau. Source owners `PNotEqualsNPDirectSATLowerBoundExact` and observer no-go remain the authentic target.
9. **Known-technique compiler work (not Clay novelty):** Karp N21 original all-word gamma/signed reader, source/target language equivalence, polynomial bit-clock and memory model; Cook–Levin typed complete compiler; E20 positive threshold and signed graph fidelity; remaining historical edges' costed correctness and 21 NP membership proofs. **Category:** source-preserving formalisation + engineering, although not trivial. Finite regression successes are not all-word proofs. The original Karp 21-node reduction graph alone does **not** imply P != NP.

### Yang–Mills (Bałaban T4 P0 -> E1/D1/D2/N1/G1)

10. **Paid finite source:** the existing generated-grid module has `256` cells, `16` all-inner, `240` regular; original `64+96+64+16=240` orbit counts are defined, and #1498 has conditional semantic seven-generator->four-representative transport. Do not re-prove those as a novel physical theorem.
11. **Conditional symmetry, not unconditional:** a coordinate flip sends an individual sine-half to its negative and can send `cos(q_mu-q_nu)` to `cos(q_mu+q_nu)`. The seven literal selected scalar equalities and original atom/environment covariance are still substantive obligations. Fixed-axis external momentum may only allow a seven-class stabiliser, not four full B4 classes. **Category:** original-source *physical* identity/equivariance, not mere renaming weld.
12. **Sine bound scope:** `4 sin²(pi x/2)>=2` is true for `x in [-1,-1/2] union [1/2,1]`, but it only concerns the unshifted q and assumes the source scaling and literal box map. Shifted `q+p` can vanish even when `q` is outer (`q=pi, p=-pi`). **Category:** elementary analytic lemma + crucial original-denominator/source identification, with a possible nonuniform singularity requiring the original IR treatment.
13. **Interval hull/real quadrature:** for numerator `[-2,1]` and denominator `[2,4]`, the sign-aware quotient is `[-1,1/2]` (not `[-1/2,1/2]`). A boxed evaluator interval is not a certified integral; real volume, midpoint/Hessian error, remainder, sign and all four actual source quadrature witnesses are missing. **Category:** integral analytic/numerical certification + source-weld, not automatically paid by denominator positivity.
14. **E1/D1/D2/N1/G1:** neither one-loop asymptotic freedom, a pointwise propagator estimate, finite cluster expansion, an isolated two-observable correlation bound, a formal OS quotient, a perturbative four-point term without controlled remainder, nor dual-Coxeter positivity establishes all the physical Clay gates. **Category:** **genuine major mathematical research** on the original infinite-volume continuum Wilson measure and all compact simple groups. Required: physical E1 constructive limit; D1 original observable uniform decay; D2 same reconstructed H spectral gap with dense-domain estimate; N1 actual non-Gaussian continuum observable; G1 universal group scope.

## Requested handoff — solve vs weld vs verify

| Priority | Exact owner/gate | Category | Required evidence |
| --- | --- | --- | --- |
| NS C/D | five Lean #51 `Clay*ToLeanDojo` / `LeanDojo*ToClay` predicates | WELD + analytic boundary | Literal R³ proof terms, pinned Lean exact target and axiom audit |
| NS periodic B | R736 signed collar + actual remote boundary flux | NEW MATH | Uniform original-source cutoff/stretching inequalities, no exponent leak |
| NS R829 | instantaneous->real trajectory reserve | NEW MATH | Actual ODE/trajectory inequality and continuation |
| RH A2 | original signed strict compensation | NEW MATH / possible NO-GO | Valid same-carrier strict sign or explicit failed route |
| RH B | original signedFifthCorrelationGapAt eventual nonnegative | NEW MATH | Source-defined functional and positive proof; attached Delta5 is false |
| RH A1/G3 | zero-shell assignment/curvature/G3 strict residual | NEW MATH | Uniform correct zero-counting and summability, final inequality |
| SAT Clay | UniversalPolynomialSATDecisionFailure | NEW MATH | For every polynomial certified decider, algorithm-dependent SAT error |
| Karp-21 | N21 parser/clock, K00 Cook–Levin, 20 edges/21 members | FORMALISATION | Same-word all-input kernel proofs and explicit polynomial resource bounds |
| YM P0 | LiteralScalarIntegrandExpression + seven source symmetries | SOURCE PHYSICS / possibly NO-GO | Literal Wilson/ghost/Haar construction and exact external momentum choice |
| YM P0 | q-hat, signed interval and four quadrature/error receipts | ANALYTIC WELD | Original denominator positivity, interval soundness and true integral certificates |
| YM E1/D1/D2/N1/G1 | continuum, decay, OS, nontriviality, universality | NEW MATH | Full physical proof for original Yang–Mills quantum field theory |
| ALL | New Agda no-go and exact negative controls | VERIFY | Local Agda 2.9 proof kernel, exact branch/head, transitive dependency/escape audit; Python regressions are supplemental only |

## Attribution and promotion

External Clay/Navier–Stokes comparator is separately attributed; Agda does not inherit Lean trust. Karp, Young, Hadamard, Newman, Wilson, Faddeev–Popov, Bałaban, OS and other primary results remain with their authors. Our exact rational negative controls and new Agda fixed-instance no-go are DASHI-source adapters. No CI requirement: a local reproducible kernel receipt takes precedence. Do not infer closure from this document, code compilation descriptions, or a clean static scanner.

## 12 November 2026 — further source-proof continuation

**Committed native proof files on Agda draft PR #1499:**

- `DASHI/Mathematics/Complexity/PNotEqualsNPFixedInstanceQuantifierNoGoExact.agda`: original `PolynomialSATDeciderCandidate` target and explicit cost-model constant-time certificates. The pointwise `∃φ ∀D` statement is refuted for each supplied truth assignment bit, without a polynomial SAT theorem.
- `DASHI/Physics/YangMills/BalabanT4TightRangeDoesNotDetermineIntegralExact.agda`: unconditional four-site finite-measure countermodel with *tight*, attained extrema 0 and 1 for both fields but sums 1 and 3. The source proof `noExactIntegralFromTightRangeAlone` refutes any exact integral estimator depending only on those extrema. This is a finite mathematical negative control, not a proof about the original physical four boxes.
- `DASHI/ClayFourFrontierNegativeControlsExact.agda` is the local golden focused import root.

**Additional Lean donor:** `chboishabba/dashi_lean4` draft PR #108, `Synthesis/RiemannContinuousFifthMomentSignAudit.lean`. It source-writes the *actual displayed continuous integral* and exact algebraic negativity implication from the two explicitly declared moment identities and a strictly positive fourth moment. The moment identities still require analytic proofs for any concrete input, and no native discrete Route-B identification is made. No cross-kernel promotion.

**New analytic NS scalar countermodel:** for (0≤t<1), (E(t)=(1-t)^{-1/2}) solves (E'(t)=E(t)^3/2), has (int_0^1 E(t)dt=2), and diverges as (t\uparrow1). At rational times (t_n=1-1/n^2), (E(t_n)=n), (int_0^{t_n} E=2(1-1/n)<2), and (E'(t_n)=n^3/2); the Python exact-rational fixture checks the closed expressions for (1≤n≤1000). This is a rigorous scalar mathematical counterexample to the *claimed inference* from finite time-integrated enstrophy and an upper cubic ODE growth bound to no blowup. It is emphatically **not** a 3D Navier–Stokes solution or a blowup construction.

**Scope correction (important):** A sound pointwise enclosure (L≤f(x)≤U) *does* certify the coarse integral enclosure (L \operatorname{Vol}(B)≤\int_B f≤U\operatorname{Vol}(B)) for a nonnegative volume measure and integrable (f). Taylor/Hessian bounds are not logically necessary for this coarse certified enclosure. They are needed only for a more precise midpoint/Taylor-type approximation or when the source's prescribed certificate requires a quantitative remainder. The new Agda four-site no-go proves inability to recover an **exact** integral from min/max alone, not inability to enclose an integral from valid range+volume data.

**Existing paid YM analytic donor discovered on current master:** `BalabanClayT4BishopRegularHatMomentumGapExact.agda` proves the source-written structural implication from a selected nonnegative outer-axis sine-square lower bound to the full canonical unshifted four-dimensional Wilson hat-momentum value. Do not count this structural sum as a remaining physical proof. Still open: source sine-to-Machin-angle identification on each actual physical box, shifted denominators, selected Wilson/ghost/Haar scalar, valid momentum convention, integrand symmetry and certified quadrature/error witnesses. The module's own status reports the physical 1D angle weld as conditional.

**P≠NP nuance:** in standard polynomial-time Turing models, if a decider errs on only finitely many strings, a finite hard-coded exception table makes a polynomial-time correct decider. Hence P≠NP implies infinitely many errors per polynomial SAT decider. The repository's abstract `PolynomialCostModel`, however, does not yet prove closure under arbitrary finite exception-table patching; the all-word bit-machine and finite-table time bound must be supplied to promote that stronger statement within *this exact model*. The direct target `∀D,∃φ_D` remains the source-owned `UniversalPolynomialSATDecisionFailure`.

### Exact pending verifier commands (local authority, not CI)

```bash
# Execute on the precise #1499 branch, not master
AGDA_JOBS=1 DASHI_NO_TMUX=1 \
  bash scripts/run_agda29_parallel_check.sh DASHI/ClayFourFrontierNegativeControlsExact.agda
python3 scripts/check_clay_four_frontier_negative_controls.py

# On Lean draft #108:
lake env lean Synthesis/RiemannContinuousFifthMomentSignAudit.lean
```

The tools were absent in the current execution container, so the two new Agda proof sources and the Lean donor remain **SOURCE-WRITTEN / GITHUB READBACK** until their exact pinned kernels check. No new `postulate`, `sorry`, unsolved meta, axiom escape, or Clay-terminal theorem has been added. Previous static scans are not a substitute for the transitive axiom audit.


## 12 November follow-up — live cross-PR audit of ALL six unsolved Clay endpoints

This paragraph supersedes any earlier static summary when newer branch heads contain
source-written advances. PR heads continue changing; record exact commits with
local kernel receipts before promoting any theorem.

### Yang–Mills — latest source donors, not five physical closures

* Agda #1444 (`research/ym-voyager2026-completeness-crosswalk-20261101`)
  now contains original 1024-bond full Wilson fibre-density/recomposition,
  source-selected finite positive partition/Bishop-apartness transport
  (`YMClayP0OriginalPartitionBishopApartnessExact` conditional on
  `OriginalWilsonToBishopScalarWeld`), three-moment original R445-vs-bare
  quantitative covariance compiler
  (`YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact`),
  original selected variable-cutoff cylinder-limit compiler,
  and a strict non-promotion negative control for mere O(1/k)
  adjacent RG increments. The latter are non-summable without a stronger
  bound, and even source-independent diminishing increments cannot
  manufacture Wilson projective consistency.
* The existing D2 finite 3-mode no-go, now strengthened with
  `noUniformPositiveReciprocalGapCertificate` in the SAME owner,
  distinguishes an invisible non-vacuum mode from a different defect:
  countably many positive modewise rates 1/(n+1) do not admit a common
  positive lower spectral bound even when their finite span is dense.
  The newly added native lemma proves the denominator-cap contradiction;
  the l2 spectral illustration is a mathematical explanatory model, not
  the actual interacting OS Hamiltonian. Local Agda receipt pending.
* Agda #1498 (later than the previous P0 ledger) has
  `BalabanClayT4RefinedSineSquareRegularBoxesExact` and
  `BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact`: true
  Bishop sine-value membership implies source-faithful **UNSHIFTED**
  Wilson hat-momentum interval soundness and positive rational lower
  interval endpoint for every regular box. The original membership
  assumptions are NOT supplied merely by a grid code. Shifted q+p
  propagators, tensor-to-scalar source, physical scalar symmetries,
  numerical Hessian/error/volume integral certificates remain OPEN.
  The old universal 2m sine-square bound must not be marked physical.
* Sibling Agda #1479 adds source-recursive typed positive division and
  Bishop semantics: reuse its checker rather than writing a second
  backend or inventing per-quotient proofs. A real branch weld is still
  required before importing it into #1498.
* The canonical #1444 five-phase ledger remains PH0–PH4 / YM01–YM10;
  23 physical producers refine those targets. Actual E1, D1, D2, N1
  and G1 all remain OPEN; the R578 seven-family scheduler and R581–R583
  finite OS/selected H1 compilers are paid *conditionally*, not as
  original physical estimates.

### Exact attached-claim countercalculations

1. **RH local sign.** A zero at beta+i gamma gives horizontal log-curvature
   contribution `-1/(sigma-beta)^2` at t=gamma. At |sigma-beta|=1/3,
   it equals -9, disproving the attachment's **lower** bound -4.
   The inequality reverses: for horizontal distance <=1/2,
   -1/distance^2 <= -4. The claimed
   `log(t/(2*pi))/(2*pi)-4>0` requires
   `t > 2*pi*exp(8*pi)`, not `t>14.13`.
2. **RH Route B:** the attachment's
   `sum_k mu(k)(gamma_k^5-E[gamma^2]gamma_k^3)e^{-2gamma_k^2 t}`
   has NOT been identified with the original Lean
   `signedFifthCorrelationGapAt` / physicalCapInterior. The
   `mu`, normalization and expectation are not sourced. If the
   expectation is a positive average over gamma_k>=gamma_1,
   then `E[gamma^2]>=gamma_1^2`, so the asserted first coefficient
   is nonPOSITIVE, the reverse of the sketch's claimed sign.
   Eventual positivity also does not imply positivity for ALL t>0.
3. **NS Periodic B:** fundamental-domain *opposite faces* cancel;
   arbitrary INTERNAL cutoff boundaries need not. Example on the
   torus: u=(sin y,sin x,0), p=0 is smooth/divergence-free, and
   `div((|u|^2/2)u)(pi/4,pi/4)=sqrt(2)/2>0`; an interior small
   box has a nonzero boundary flux. A claimed torus
   `dist(x,Sigma)^(-3)` tail does not cure the missing R736 estimate.
4. **NS R829:** BKM is a **conditional criterion**, requiring the
   time integral of spatial supremum vorticity, not a source-free
   conclusion from Leray energy. Neither a Morrey small collar
   (chosen in response to an uncontrolled norm) nor an instantaneous
   negative rate is a global continuation theorem.
5. **YM quadrature:** the displayed second-order `M*diam²/24`
   error requires *centered midpoint nodes* on axis-aligned symmetric
   boxes and actual smoothness/Hessian hypotheses. Without midpoint
   nodes, `f(x)=x` on [0,1] has Hessian 0 but endpoint sample 0
   and exact integral 1/2. The correct Taylor remainder proof is
   obtained by integrating `f(x)-f(c)-Df(c)(x-c)` over each symmetric
   cell: the linear term vanishes, and
   `|error| <= M/24 * Volume * sum_i h_i^2` for cell side lengths
   `h_i`. This is a mathematical lemma template; selected physical
   original four-integrand Hessian majorants remain absent.
6. **YM D2:** density of a positive-time cylinder span does not
   alone imply a positive spectral gap. The countable selfadjoint
   diagonal model `H e_n= e_n/(n+1)`, `H Omega=0` on l2 has
   dense finite-support tests and individually positive decay rates
   tending to zero. Need one **uniform bound** on SAME reconstructed
   nonvacuum sector, not just density. Its integer denominator-cap
   no-go is source-written in #1444.
7. **YM E1/N1/G1:** a prescribed running `g^2(a_k)~1/k`
   fixes neither a coherent interacting continuum measure nor
   scale-uniform Wilson three-moment discrepancy, genuine four-point
   remainder, or full compact-simple-group estimates. A positive
   one-loop beta coefficient is not an implication to these gates.

The additional independent test runner
`scripts/check_clay_latest_attached_maxcut_20261112.py` contains nine
negative-control groups. A matching stand-alone local reference runner
completed all nine; the GitHub blob still needs an exact checkout replay.
None of these mathematical negative controls is a Clay solution.

### Other Clay projects checked, outside attachment's four

* **P vs NP:** newest Agda #1474 contains source-written physical bit-tape,
  positive-threshold bit-width bound, and a fail-closed local
  `referee_karp21_maxcut.sh kernel-cut` workflow. Its owner explicitly
  states F2 peak allocation, F1/F3/F4 machine simulation/clock,
  `PR.InNP`, E20/Cell-Bits, other reductions and universal `SATNotInP`
  remain OPEN, **not** 21 verified NP-completeness results.
* **BSD:** Lean #107 now owns actual geometric E[2] Galois-equivariance,
  Ebar doubling continuous TopRep and a concrete two-way rational-curve
  vs area-one right triangle weld; rank-zero is conditional on a
  missing formally proved infinite descent. Still open all-place
  cohomological Kummer/Sha(E)[2], genuine L(E,1) same-curve
  modular/Mellin identity and nonvanishing, odd-primary/leading
  coefficient and universal BSD. The Lean v4.35-v4.28/mathlib mismatch
  is an explicit *verification* blocker, not an analytic theorem.
* **Hodge:** Lean #40 merged genuine scheme-level algebraic cycle
  pushforward/automorphism donors. Actual P1 x P1 cycle-class action
  and primitive general Hodge algebraicity are OPEN.
* **External NS C:** Lean #109 still leaves four literal R3 Fefferman-C
  representation leaves and the finite-energy scalar-to-vector norm
  bridge (after adding same-solution smoothness); the attachment's
  torus weak-Leray dictionary does NOT inhabit these R3 leaves.
* **RH:** Lean #50 A1 shell/curvature, A2 strict debt/compensation,
  Route B boundary/sign/limit are still real analytic source leaves.
  Lean #108 audits a different continuous even-moment functional.

### Required next outputs rather than more wrappers

1. Agda: run the exact #1444 D2 negative-control owner and imported
   source closure with pinned Agda 2.9; check transitive postulates
   and do NOT equate a proof under `RealAnalysisAxioms` with a
   constructive Bishop theorem.
2. Agda #1498: source-inhabit original four-diagram Wilson/ghost/Haar
   scalar and its tensor-to-beta projection; then test true
   external-momentum covariance and shifted denominator positivity.
   Only then produce four actual midpoint/Hessian/volume/error
   quadrature certificates.
3. Agda #1444: pay ORIGINAL cutoff-dependent bounded three-moment
   estimates with a genuinely summable physical scale/UV/IR budget,
   original full Wilson small+large field, and same-S_OS dense
   nonvacuum spectral bound. Physical G1 and N1 remain independent.
4. Lean #109: close *literal R3* five transport leaves; local
   exact-head typecheck + `#print axioms`. Avoid importing a
   torus weak-solution result as an R3 theorem.
5. Lean #50: decide A2 strict residual sign and/or A1 summation
   source; Route B must use its original `physicalCapInterior`.
6. Agda #1474 / Lean #107: local native kernel verification at the
   pinned original toolchains, while retaining their independent
   mathematical P!=NP and universal BSD obstructions.

No new endpoint is promoted. Full original source/physical authority,
Agda golden local kernel and Lean cross-prover transport remain distinct.


### Final current heads after latest physical-source audits (11:18 UTC)

* **YM #1498 `13dbfa361d30`** now has exact source rank-endpoint
  generator invariances, a formal rank-one naive-squaring counterexample
  and four rational *auxiliary unshifted inverse-propagator* intervals
  folded over 240 boxes. These ARE NOT the original four-diagram
  Wilson/ghost/Haar beta quadratures or actual integral error receipts.
  Physical source sine-value membership, shifted denominators, tensor
  scalar projection and true quadrature still OPEN.
* **YM #1444 `a6e2ee14733c`** contains the original D2 reciprocal
  denominator uniform-gap no-go just added to the existing owner
  plus the updated PH0–PH4 roadmap. Local Agda kernel pending.
* **Karp #1474 `00556cd11bf5`** source-writes exact physical gamma
  sixteen-dispatch cases, original accepted-witness bitword width,
  and tighter `2m≤|G|` G3 certificate accounting. This is a
  source-written **G3 memory/witness weld**, not a full F1–F4
  machine-clock, Cook–Levin, 21-completeness or SATNotInP proof.
* **BSD Lean #107 `96d1a0ea2422`** advances actual Ebar continuous
  linear [2] exactness, selected point-H1 localization and exact
  Γ(1/4) target positivity. Genuine all-place Kummer/Sha comparison,
  same-curve L(E,1) Mellin and Fermat/MW rank remain OPEN.
* Hodge Lean #40 remains merged genuine algebraic-cycle donor, not
  universal Hodge; NS Lean #109 five R3 transports pending; RH
  Lean #50/Agda #1434 original strict analytic inequalities pending.


## 12 November broad PR continuation / 34 original producer gates

After reviewing the first 100 open Agda PRs and all 59 open Lean PRs, the source-native detailed continuation is `Docs/roadmaps/ClayBroadPRExactRemaining20261112.json`, with independent fail-closed validator `scripts/check_clay_broad_maxcut_manifest.py`. This ledger counts **34 remaining specific proof producers** across the six open Clay problems plus the shared world-builder dependency; it does NOT imply 34 new Clay endpoints or 34 proofs solved. The 34 IDs are finer-grained than the original physical Yang--Mills YM01--YM10 owner IDs / 23 producer manifest; neither is superseded. The ledger keeps source-written, local, kernel and physical/integrated gate status separate. All 34 named remaining terminal producers are OPEN.

Yang--Mills Agda #1498 now source-writes the actual 240-cell free-Wilson auxiliary four-orbit rational bounds and `BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact` with the exact unit Brillouin `d⁴k/(2π)⁴ = d⁴x/16` convention and endpoints `15/256,6592/22707` for **regular free 1/hat(k)² only**. Independent Fraction enumeration verified 256 cells, 240 regular, 16 infrared, the orbit counts and the source coefficients. The four physical one-loop Wilson/ghost/Haar integrals are **not** thereby certified. Original physical sine membership, shifted propagators, genuine scalar AST/derivatives, symmetry and quadrature errors remain open. Source contribution: [Agda #1498](https://github.com/chboishabba/dashi_agda/pull/1498).

Yang--Mills Agda #1444 has independently advanced the *nonperturbative* original full 1024-bond positive-Wilson Haar-fibre disintegration, partition and covariance machinery; that does not prove small original RG cross-numerator, E1 cutoff convergence or D2 same-H gap. Do not conflate finite blocked Wilson partition identity with the perturbative free-propagator calculation. Likewise Lean #107 genuinely constructs Ebar exactness and positive Gamma **candidate**, not classical Sha nor the original L(E,1) Mellin identification; merged Lean #40 already represents the selected P¹×P¹ and real ruling-cycle swap, leaving its standard geometry instances, cycle-class naturality and universal Hodge problem, not an absent P¹ scheme.

**Local, no CI:** run `python3 scripts/check_clay_broad_maxcut_manifest.py`; separately run the existing per-branch pinned checker on the actual Agda #1498, #1444, #1474 and Lean #107/#109 exact checkout. No kernel or physical completion is implied by the ledger validator. The Agda golden proof authority and original-source attribution remain unchanged.
