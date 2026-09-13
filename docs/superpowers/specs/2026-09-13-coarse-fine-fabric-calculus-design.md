# Coarse/Fine Fabric Calculus Design

## Goal

Consolidate the existing coarse/fine, observer, NDim, and wave-refinement machinery through the smallest shared theorem surface already justified by the repository, without introducing a parallel Pi/Phi/Psi ontology.

## Existing canonical roots

The tranche treats these owners as authoritative inputs:

- `DASHI.Core.CoarseFineRelativeFibreExact`
- `DASHI.Core.ConsumerRelativeReductionKernelExact`
- `DASHI.Core.ObserverFactorizedRefinementExact`
- `DASHI.Core.FibreRestrictionCore`
- `DASHI.Core.NDimParetoHyperfabricExact`
- `DASHI.Biology.JCoarseFineConsumerReductionBridgeExact`
- `DASHI.Physics.ShiftWaveRefinementSeam`

The design does not replace any of them.

## First shared theorem family

The first new domain-neutral surface is static projection loss / consumer non-factorability.

For a projection `project : Fine -> Coarse`, if two fine states have the same projection but a consumer distinguishes them, then that consumer cannot be represented by a coarse-only observation. This is already present concretely in `FineSensitiveConsumer` / `fineSensitivityRefutesCoarseOnlyReduction`; the new owner should expose the theorem in a projection-oriented form reusable by non-`CoarseFineReopening` lanes.

The theorem must not assume an exact reopening. Exact reopening remains additional structure supplied by `CoarseFineRelativeFibreExact` when available.

## Three initial manifestations

1. **JCoarse/JFine** reuses the existing `jFineSensitiveConsumerRefutesJCoarseOnly` path rather than re-proving J-specific geometry.
2. **NDim** treats `AxisProjection` as a restriction/observer. The adapter must preserve the existing boundary that projected dominance does not imply full dominance automatically. No cardinality/dimension identification is introduced.
3. **Wave refinement** adapts the existing refinement seam only where there is an actual pair of states/observations witnessing loss or factorisation. If the current wave owner does not expose enough structure, the adapter records an explicit unpaid seam instead of inventing one.

## Dynamics stays separate

Static nonrecoverability and dynamic noncongruence are distinct. This tranche may expose a typed placeholder/status for a future dynamic theorem, but it must not derive dynamic failure from static failure.

A later tranche may generalise the existing positive `CoarseDynamicsClosure` square and the wave transport residual/defect machinery.

## 369 / NDim boundary

`PNFHyperfabric369` and `Base369NDimParetoChartExact` are downstream candidates. This tranche does not make 369 the generic fabric. The next tranche may adapt 369 only after the generic projection-loss theorem has three real consumers.

## Status / WrongType requirements

The implementation must preserve:

- coarsening != refinement != reconstruction;
- projected validity does not imply full validity;
- dimension != state count != candidate count != carrier identity;
- static nonrecoverability != dynamic noncongruence;
- JCoarse/JFine is an instance, not the universal fidelity hierarchy;
- source/provenance or analogy is not proof of factorisation.

## Testing

Use TDD. Add a regression owner first that imports the intended production owner and requires the generic projection-collision theorem plus the three adapter/status surfaces. The regression must be structurally RED before the production owner exists. Then add the minimum implementation and verify through the repository's available Agda/static CI surfaces. If no Agda-capable runner exists for the branch, report compilation as inconclusive rather than promoting static checks to kernel certification.

## Rollup

Wire only into a narrow existing `Everything`/core rollup that already contains these owners. Do not add a giant default build target.
