# Verification and quality gates

[Back to the contract overview](README.md)

## Testing phase after every development lane

Every development lane returns evidence to the orchestrator. No lane is promoted directly into the terminal theorem.

The orchestrator then runs this sequence:

1. **Source-fidelity review**
   - Check the theorem statement against the official Fefferman clause it implements.
   - Check author, title and DOI or official-source identifier.
   - Reject any extra smallness, symmetry, mean-zero, alignment or residence hypothesis unless it is explicitly a proved reduction.

2. **Mathematical type review**
   - Check signs, quantifier order, cutoff indices and units.
   - Check Navier–Stokes scaling.
   - Check whether constants are independent of shell cutoff, Galerkin cutoff and maximal time.
   - Check that every positive source and residual has a named constructor.

3. **Counterexample and falsification review**
   - Test the smallest nontrivial Fourier and rational models.
   - Test high-high to low and high-high to zero output.
   - Test zero-gap hysteresis and amplitude scaling.
   - Reject a proposed coercive estimate when a finite witness breaks its sign or uniformity.

4. **Static repository audit**
   - Reject postulates, holes, unsafe options, trust primitives, termination escapes and placeholders.
   - Verify exact theorem names, source identifiers and authority-boundary markers.
   - Verify that every new document is linked from a parent by a relative path.

5. **Cumulative kernel check**
   - Run the Round 23 checker, which first runs the Round 22 checker and then typechecks the Round 23 validation root with pinned Agda 2.9.
   - A failed or absent kernel result leaves the lane unpromoted.

6. **Integration review**
   - Confirm that the new result changes at least one requirement state from `physicalProducerOpen` to `checkedReducer`, or produces a valid falsification that narrows the route.
   - Confirm that no held terminal lane was rewritten without a concrete integration defect.

## Queue quality metrics

Refinement continues only when at least one metric improves materially.

| Metric | Improvement condition |
|---|---|
| Load-bearing open clauses | Decreases by at least one. |
| Unnamed residuals | Decreases, never increases. |
| Cutoff-dependent constants | A dependency is removed or proved necessary. |
| Viscosity margin | A new explicit allocation is added without reaching or exceeding one. |
| Circular hypotheses | A target norm, BKM norm, alignment or residence assumption is removed. |
| Falsification power | A proposed theorem receives a smaller exact counterexample harness. |
| Kernel coverage | A new module enters the cumulative root and typechecks. |
| Source traceability | Every theorem gains a primary source or is marked repository-original. |

Progress has plateaued when no open clause changes state, no new exact counterexample narrows a claim, and no missing dependency is made more explicit.

## Round 23 test targets

The checker must confirm these exact artifacts:

- `NSTriadKNFeffermanPeriodicClayStatementExact.agda`
- `NSTriadKNLuoPeriodicMeanZeroGalileanReductionExact.agda`
- `NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact.agda`
- `NSTriadKNLuoClayEndToEndCompositionRound23Exact.agda`
- `NSTriadKNLuoClayPrePostInvariantContractRound23Exact.agda`
- `NSTriadKNLuoClayContractRound23Validation.agda`
- `DASHI/Papers/NavierStokes/ClayContractRound23.agda`
- `DASHI/Papers/NavierStokes/TheoremInterface.agda`
- `docs/ns-clay-contract/README.md`
- `docs/ns-clay-contract/requirements.md`
- `docs/ns-clay-contract/architecture.puml`
- `docs/ns-clay-contract/governance.md`
- this verification document

The exact theorem markers are:

- `FeffermanPeriodicClayStatementB`
- `meanZeroSolverAndGalileanRestorationGiveClayB`
- `legacyWitnessGivesLiteralFeffermanWitness`
- `inRepoPathClosesLiteralFeffermanPeriodicB`
- `canonicalClayPreconditions`
- `canonicalClayPostconditions`
- `canonicalProofRouteInvariants`
- `canonicalNSClayContractRound23Status`
- `nsPaperLiteralClayTargetImplemented`

## Current validation boundary

Static checks and connector-visible repository inspection can be completed in this turn. A successful Agda kernel result or GitHub Actions run is reported only when an actual run is visible. Code review bot success is not a substitute for kernel typechecking.
