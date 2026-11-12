# Odd zeta irrationality × Bishop × C3: source-preserving max-cut

## Attribution and scope

- **External mathematics:** Wadim Zudilin, *One of the odd zeta values from zeta(5) to zeta(25) is irrational*, arXiv:1801.09895. The July 2026 Lean/Mathlib manuscript supplied by the user reports the fallback window through zeta(33), using Hanson's elementary lcm bound. This is an external result, **not** an original DASHI theorem.
- **External formalization:** exact GitHub repository, revision, declaration, axiom list, and theorem-to-`riemannZeta` identification are **not yet admitted**. Do not describe a screenshot as a retrieved or kernel-checked source file.
- **Existing DASHI work:** `DASHI/Foundations/BishopGoldenRatioCarrierExact.agda` supplies a Bishop carrier for phi; `DASHI/Moonshine/QuadraticIrrationalSignedApproximationFibreExact.agda` keeps rational approximation separate from exact irrational targets; `DASHI/Analysis/RiemannAnalyticSubstrate.agda` specifies, but does not construct, the actual completed zeta analytic layer; `DASHI/Moonshine/C3RiemannConjugationBridgeExact.agda` proves a *coordinate* reflection/conjugation relation, not a zeta-zero theorem.
- **New DASHI contribution:** `DASHI/Analysis/ZetaOddValueWitnessTransportExact.agda` derives disjunctive irrationality transport along explicitly provided equalities in one selected value carrier, with preserved witness index. It does not supply the equalities.

## Max-cut dependency graph

```text
External Lean theorem at an exact revision [OPEN]
             |
             v
Lean's selected zeta definition -> actual positive-odd Dirichlet values [OPEN]
             |
             v
Lean values == Bishop values on same carrier [OPEN]
             |
             +-----> generic witness transport [CODE ADDED; TYPECHECK PENDING]
             |
             v
Bishop values == DASHI analytic substrate values [OPEN]
             |
             v
DASHI odd-zeta irrationality witness [CONDITIONAL]
```

The independent C3/xi conjugation and orbit-shape comparisons are not inferred from irrationality, and do not discharge RH Weil positivity.

## Proof ledger (no promotion without admission)

| Gate | Exact obligation | Status |
| --- | --- | --- |
| ZI00 | Inspect external Lean repository/commit, check theorem statement, `#print axioms`, and provenance | OPEN |
| ZI01 | Match the 15 argument indices `5 + 2*k`, `k : Fin 15` to the external finite set | OPEN |
| ZI02 | Identify Lean real/complex zeta values with selected Bishop-real values | OPEN |
| ZI03 | Identify Bishop-real values with genuine DASHI analytic zeta values | OPEN |
| ZI04 | Preserve an existential irrationality witness along explicit equality | IMPLEMENTED, NOT TYPECHECKED |
| ZI05 | Verify direct vs via-Bishop commutation on the same witness index | IMPLEMENTED, NOT TYPECHECKED |
| ZI06 | Ingest source provenance and proof dependencies into canonical world admission | OPEN |
| ZI07 | Integrate genuine accepted theorem into public `ZetaTheoremSurface` | BLOCKED ON ZI00–ZI03 |
| ZI08 | Evaluate reusable Stirling, factorial, LCM and rational-separation lemmas against Bishop/golden-ratio approximation libraries | OPEN |
| ZI09 | Preserve C3 orbit-shape non-identification and RH/Weil analytic gates | MAINTAINED BOUNDARY |

## Golden-ratio and irrational-number cross-pollination

The relevant transferable design pattern is not equality of phi and odd zeta values. It is:

1. Rational presentations/finite approximations must not be confused with an irrational analytic target.
2. Embeddings and actual value equalities carry theorem transport, not matching names, decimal approximations, or abstract isomorphism.
3. A signed approximation defect, a lower bound, or an algebraic minimal polynomial is evidence for its *own selected value*, not for unrelated zeta values.
4. Reuse exact proof objects and source identities through fibres/provenance; do not duplicate carrier definitions or hide imported hypotheses.
5. The golden ratio is algebraic irrational; irrationality alone does not characterize an odd zeta value or establish transcendence.

## Verification protocol

No repository-local Agda compiler is available in the current execution environment. Run the repository's pinned Nix/Agda environment (not a generic latest Agda) and type-check the new module with the established include paths. Do not label ZI04/ZI05 'machine-checked' until successful. Then add a source-pinned external Lean artifact and separately discharge ZI01–ZI03.

## Attribution references

- W. Zudilin, arXiv:1801.09895: https://arxiv.org/abs/1801.09895
- Existing exact phi carrier: `DASHI/Foundations/BishopGoldenRatioCarrierExact.agda`
- Existing rational-approximation fibre: `DASHI/Moonshine/QuadraticIrrationalSignedApproximationFibreExact.agda`
- Genuine zeta boundary: `DASHI/Analysis/RiemannAnalyticSubstrate.agda`
- C3 coordinate boundary: `DASHI/Moonshine/C3RiemannConjugationBridgeExact.agda`

## Additional candidate external proof (not admitted)

The public `telaviv/zeta-irrationality` README reports an unconditional Mathlib theorem `ZetaIrr.Z7.oneOfZeta7To21` proving that one of zeta(7),...,zeta(21) is irrational, with exactly `[propext, Classical.choice, Quot.sound]` as reported axioms. URL: https://github.com/telaviv/zeta-irrationality . Its actual commit and source declarations have not been fetched or checked here. As the set {7,...,21} is a subset of {5,...,33}, an eventual verified witness can map into the existing 15-index `OddWindow`, but a proper finite-index embedding theorem is still necessary (ZI01).

The separate 2026 individual zeta(5) projects must not be treated as automatically interchangeable. For example, https://github.com/danromik/zeta5-irrationality reports a prime-number-theorem axiom, whereas https://github.com/long-mathematics/zeta5-irrationality explicitly says it has not yet proved the endpoint. Verify every project's own trust boundary before admitting a claim. These are external projects; no credit is transferred to DASHI.
