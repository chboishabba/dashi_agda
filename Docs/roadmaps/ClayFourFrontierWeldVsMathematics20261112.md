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
