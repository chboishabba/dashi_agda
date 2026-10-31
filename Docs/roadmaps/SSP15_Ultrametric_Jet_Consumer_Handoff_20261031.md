# SSP15 / ultrametric / C3 winding — user verification handoff (2026-10-31)

## Ready-to-inspect source hierarchy

1. Canonical real signed SSP owner: `DASHI/Biology/SignedSSPFRACTRANWeaveExact.agda` (`SSPPrime`, `SSPValuation`, `SignedMultiplicity`, `coarseMultiplicity`, `orientationOfMultiplicity`).
2. Original 369 ultrametric: `DASHI/Geometry/SSP369Ultrametric.agda` (prefix/depth, `distance-zero→equal`, triangle); `DASHI/Geometry/Admissibility369UltrametricBridge.agda` (existing jet-depth owner).
3. New exact **actual-valuation** BIDI: `DASHI/Biology/SSP15SignedHistoryConsumerBidiExact.agda` imports native `SSPValuation`, keeps sign orientation *and the original full signed valuation* as the residual. `decodeEncode`, `consumerFactorsThrough`, `retainedObserverSufficient` and `signCollisionForcesSignedResidual` are source-level constructors/proofs. This is intentionally not pretending sign-only reconstruction or bounded fixed-depth completeness.
4. Prior conditional fine-address and seam transport: `DASHI/Core/TwinPickoverHypervoxelAdmissibleJoinExact.agda`, `DASHI/Core/TwinPickoverHistoryHypervoxelTransportExact.agda` and `DASHI/Geometry/SSPJetExistingOwnerTransportExact.agda`.
5. Exact finite C3 jet certificates: `scripts/check_ssp15_c3_winding_jet_rank.py`, `scripts/check_ssp15_c3_winding_adjugate_inverse.py`, `scripts/check_ssp15_c3_winding_modular_inverse.py`. Locally independently checked: selected rows `0..14`, `det=-68973567202690493145068231495208746474043983233237147979454873600000000`, `det mod101=98`, rank of nine-jet matrix 14. These are finite mathematical identities; not kernel-checked Agda matrix proofs.

## No-CI local verification (run yourself)

From repository root, on branch `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028`:

```bash
python scripts/check_ssp15_c3_winding_jet_rank.py
python scripts/check_ssp15_c3_winding_modular_inverse.py
python scripts/check_ssp15_c3_winding_adjugate_inverse.py
agda -i . -i /path/to/agda-stdlib DASHI/Biology/SSP15SignedHistoryConsumerBidiExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Geometry/SSPJetExistingOwnerTransportExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Core/TwinPickoverHypervoxelAdmissibleJoinExact.agda
```

Use the repository's own `agda-lib` configuration and vendored dependencies if available instead of the illustrative stdlib include argument. Commands are **not claimed executed** here. In particular, this module's original `SignedSSPFRACTRANWeaveExact` import is not marked `--safe`; resolve any import/safety boundary by auditing and migrating the canonical owner, not by an unsound extra `--safe` pragma.

## Exact remaining acceptance (no false terminal claims)

- A finite-matrix Agda/Lean proof for ten-derivative SSP15 C3 injectivity (e.g. selected determinant 98 mod101), plus a canonical signed-valuations-to-exact-jet adapter. The Python adjugate inverse is already specified for all inputs.
- A nontrivial *compressed* residual sufficient for a specified consumer; the new concrete original-valuation residual is deliberately lossless and maximal, not minimal.
- Typecheck/repair source-written Agda files, verify no holes/postulates, and align any Lean shadows.
- For twin primes: real `Lambda(n)Lambda(n+2)` pair source, no-wrap DFT theorem, and a new prime-specific unbounded correlation/lower bound.
- For Pickover: actual Bishop `sin(99^(9999!))` rigorous phase interval excluding zero.
- For RH: genuine zero-exclusion analytic estimate.
The last three are open analytic problems and cannot be filled by asserting finite hyperfabric equivalence.

## Attribution / limits

Mathematical provenance and original in-repo owners preserved; see canonical twin-prime/Pickover steelmen and max-cut remaining-lemma register. No ESD content modified. No CI, Agda or full script execution receipt has been claimed. Source-written is not kernel-verified.
