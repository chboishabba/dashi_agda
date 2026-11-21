# Alpöge/Claude RH–GRH × DASHI geometric transport (21 November 2026)

## Provenance and status

External claim: Levent Alpöge's 20 Nov 2026 announcement at https://alpo.ge/remark.pdf and byte-exact mirror https://github.com/Deicyde/riemann-hypothesis. MIT independent audit: https://math.mit.edu/~drew/grh/ (snapshot 20 Nov 22:05 UTC). The MIT audit reports compilation of 175,187 modules, leanchecker replay, con-leche and nanoda independent kernel acceptance, con-leche statement comparison against a separate challenge and only Lean foundational axioms. Further checks remained underway at that timestamp. These receipts were **not executed locally by DASHI**.

The five audited statements include Mathlib RiemannHypothesis and Dirichlet L-function zero-location/nonvanishing claims. This is **Dirichlet GRH**, not the extended hypothesis for all Dedekind or automorphic L-functions.

## New source owner

`DASHI/Analysis/AlpogeGRHGeometricTransportExact.agda` supplies `ExternalRHGeometricTransport` and `externalRHImpliesDashiRH`.

This is a deliberately conditional **typed transport theorem**, not an imported Lean proof, not a completed proof of DASHI's analytic substrate, and not a fresh Agda kernel acceptance. It demands three separable items: an external zero-location theorem; a same-object map from DASHI's complex plane to the Lean complex plane preserving nontrivial zeta zeros; and reflection of the critical-line predicate. There is no fabricated constructor.

## Integration map

1. **RH zero-location lane**: when an audited certificate for `leanRH` and an actual same-object transport are available, `externalRHImpliesDashiRH` discharges `RiemannHypothesisFor analytic` without re-proving zero-location.
2. **Our Weil/geometry lane**: `DashiWeilSquareBridge.agda` derives RH from convolution-square positivity plus an off-line separator. External RH does **not** construct `WeilPositiveDecomposition`, `DashiWeilSquareEncoding`, `WeilSquareOffLineSeparator`, a positive 3×3/3×3×3 geometry, or a spectral Gram identity. The reverse RH→Weil-positivity equivalence requires a separately identified genuine explicit-formula theorem and matching test spaces.
3. **Bishop/complex analysis**: external RH does not supply our constructive complex exponential/logarithm, finite rectangle-tail limits, or selected Kneser branches. Reuse only through exact function-identification lemmas.
4. **Karp-21 / algorithmic corollaries**: GRH-conditional primality, prime-in-progression and finite-field algorithms can be tracked as corollaries *after* their exact statements and complexity bounds are imported. Neither P≠NP nor the Karp native verifier gates follow.
5. **BSD / elliptic curves**: Dirichlet GRH is not GRH for all elliptic curve L-functions and does not settle BSD, Mordell–Weil rank, Sha, or leading coefficients.
6. **YM/NS/TSVF/KK**: no direct transfer to Clay Yang–Mills mass gap, 3D Navier–Stokes, or a measured microscopic Lorentz metric.

## Exact acceptance gates

- [ ] Freeze source archive SHA-256 and challenge export SHA-256 from the independent audit; maintain byte-exact, trusted source provenance and license separation.
- [ ] Reproduce checker verdicts on pinned Lean 4.33.1/Mathlib 4.33.1 and independent judge, including axiom audit, namespace/definition resolution, and challenge/solution comparison.
- [ ] Read the original proof's dependency graph: identify its *actual* geometric/analytic proof steps, rather than treating kernel acceptance as an explanation of mechanism.
- [ ] Produce independently checked `LeanNontrivialZero` and `LeanCriticalLine` matching the audited Mathlib theorem.
- [ ] Implement actual `toLean`, `zeroPreserved`, and `criticalLineReflected` against the original analytic substrate, not a record of unrelated abstract sets.
- [ ] Compile the new Agda source with the repository's pinned toolchain and publish a local exact-head kernel receipt.
- [ ] If pursuing geometric mechanism, separately prove RH→positive Weil square form on the genuine source test-function space and identify it with DASHI's spectralZeroForm. Maintain the existing coercivity and separator gates as open until directly discharged.

**Do not claim** that this conditional bridge imports an external proof or proves RH in Agda. It is a fail-closed consumer for such an import, with geometric dependencies explicitly preserved.
