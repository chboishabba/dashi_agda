# Agda Validation Targets

Purpose: keep the validation manifest aligned with the live NS/YM/unification
frontiers and the current aggregate check policy.

## Reading Rule 2026-06-12

This manifest distinguishes:

- current canonical frontiers
- downstream consumer surfaces
- historical route receipts that should still typecheck but are no longer the
  best statement of the live frontier

Current canonical reading:

- NS: explicit candidate self-contained packet is recorded; live burden is
  promotion evidence / referee-grade acceptance around the exact consumed
  `A1/A3` and `A4` inputs, not missing theorem-shape grammar.
- Unification: explicit candidate `UCT.1-UCT.8` package is recorded; the live
  wall is `UCT.1-UCT.4`, with `UCT.5-UCT.8` as structured downstream
  consumers.
- YM: the genuine remaining missing-content burden is the Balaban-centered
  `H3a` cluster if internal closure is demanded.

## Aggregate Check Policy

Use two tiers only:

1. Targeted heavy-frontier smoke checks:

```bash
timeout 15s agda -i . <module>.agda
```

2. Aggregate repo check:

```bash
agda -i . DASHI/Everything.agda
```

Interpretation:

- Exit `124` on a targeted check means budget exceeded, not a type error.
- A targeted pass does not promote any theorem or clear any authority blocker.
- The aggregate check is green only when `DASHI/Everything.agda` passes.
- The aggregate check is a compile-integration signal only; it does not change
  fail-closed promotion flags.

## Promotion Probes

Use the probe layer to extract the minimal root-level blocker cutset without
mass-flipping receipt booleans across the repo.

Probe modules live under `DASHI/Physics/Probes/` and are intentionally not
imported by `DASHI/Everything.agda`.

Compile surfaces:

```bash
agda -i . DASHI/Physics/Probes/NSPromotionProbe.agda
agda -i . DASHI/Physics/Probes/YMPromotionProbe.agda
agda -i . DASHI/Physics/Probes/UnificationPromotionProbe.agda
agda -i . DASHI/Physics/Probes/CurrentProofProfilePromotionProbe.agda
agda -i . DASHI/Physics/Probes/AllProbes.agda
```

Operational runner:

```bash
bash scripts/run_promotion_probe_cutset.sh
python3 scripts/promotion_probe_cutset_harness.py --json
```

Interpretation:

- `DASHI/Everything.agda` should stay green.
- The probe modules are allowed to fail.
- Each probe is designed to fail at the first strengthened root assertion that
  the current canonical receipt does not yet satisfy.
- This reduces the search space from many historical `false` witnesses to a
  small root-level blocker map.

## Canonical Frontier Targets

Validate these in routine loops because they sit on the current walls.

### NS wall: coupled `A1/A3` bootstrap plus quantitative `A4`

- `DASHI/Physics/Closure/NSAbelTriadicDefectMeasureConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSAbelTriadicStationarityConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSBoundedAbelMassEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianOutputSupportTransferBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianFourierOutputCouplingBoundary.agda`
- `DASHI/Physics/Closure/NSA5KappaBiasVanishingFromA4StationarityBoundary.agda`
- `DASHI/Physics/Closure/NSPointwiseToAbelCompositeA6Boundary.agda`
- `DASHI/Physics/Closure/NSA7ResidualDepletionGronwallBoundary.agda`
- `DASHI/Physics/Closure/NSA8A9MonotonicityClosureTheoremLadderBoundary.agda`
- `DASHI/Physics/Closure/NSWriteupAndConstantsReadinessBoundary.agda`
- `DASHI/Physics/Closure/NSStandardPDEWriteupAssemblyBoundary.agda`
- `DASHI/Physics/Closure/NSPaperSubmissionPacketBoundary.agda`

Operational reading:

- The live mathematics is `A1/A3` plus the uniform `A4` transfer.
- `A5-A9` are downstream consumers and should stay checked as dependency
  integrity, not as independent closure claims.
- NS writeup/packet surfaces may be authority-audited or submission-ready
  while `Proved = false` and Clay promotion remains false.
- Older Sprint 64-67 CKN-route receipts remain useful regression/history
  surfaces, but they are not the canonical current statement of the NS
  frontier and should not displace the packet surfaces above.

### YM wall: `H3a` transfer, then `H3b`, then no-spectral-pollution

- `DASHI/Physics/Closure/YMSprint109NoBottomSpectrumPollutionCompactness.agda`
- `DASHI/Physics/Closure/YMSprint109MoscoSpectralLiminfAssembly.agda`
- `DASHI/Physics/Closure/YMSprint119MoscoAllObligationsReducer.agda`
- `DASHI/Physics/Closure/YMSprint119TransferCalculusAllObligationsReducer.agda`
- `DASHI/Physics/Closure/YMBruhatTitsToOSLatticeTransferBoundary.agda`
- `DASHI/Physics/Closure/YMSpectralMarginToContinuumTransferCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/YMReflectionPositivityFullTheoremAssemblyBoundary.agda`
- `DASHI/Physics/Closure/YMContinuumMassGapFinalAssemblyBoundary.agda`
- `DASHI/Physics/Closure/YMOnlyRemainingAuthorityBlockersBoundary.agda`
- `DASHI/Physics/Closure/YMStandardLanguageWriteupReadinessBoundary.agda`
- `DASHI/Physics/Closure/YMPaperSubmissionPacketBoundary.agda`
- `DASHI/Physics/Closure/YMExternalAcceptanceBoundary.agda`
- `DASHI/Physics/Closure/YMFinalAuthorityPackagingCompositeLightweightBoundary.agda`

Operational reading:

- Mosco/liminf compactness is necessary but not the wall.
- `H3a` is the load-bearing transfer input.
- `H3b` and no-spectral-pollution are downstream of `H3a`.
- RP/OS/Wightman remain explicit authority-side blockers even where theorem
  assembly and packet surfaces are audited or submission-ready.
- Older Sprint 88/89/99/126/127 ledgers remain useful historical route and
  acceptance surfaces, but they are not the best current statement of the YM
  frontier.

### Unification wall: `U-1a-H` through Jordan-von Neumann, then authority

- `DASHI/Physics/Closure/UnificationScaleInvariantCrossTermHypothesisBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHJustificationNSLaneBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHJustificationYMLaneBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHJustificationGlobalBoundary.agda`
- `DASHI/Physics/Closure/UnificationU1aHPerLaneCompositeBoundary.agda`
- `DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda`
- `DASHI/Physics/Closure/UnificationNullClassSubspaceCompleteBoundary.agda`
- `DASHI/Physics/Closure/UnificationParallelogramFromBilinearBoundary.agda`
- `DASHI/Physics/Closure/UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary.agda`
- `DASHI/Physics/Closure/UnificationSignatureCliffordConsumerSocketBoundary.agda`
- `DASHI/Physics/Closure/UnificationLaneJustificationAuthorityBoundary.agda`
- `DASHI/Physics/Closure/UnificationConsumerAuthorityAssemblyBoundary.agda`
- `DASHI/Physics/Closure/UnificationAuthorityReviewPacketBoundary.agda`

Operational reading:

- The live unification wall is not "generic full unification".
- The first real theorem burden is `U-1a-H`: the scale-invariant cross-term
  decomposition that can feed cross-term nullity.
- Cross-term nullity must feed modulo-null linearity, four-point cancellation,
  parallelogram, and Jordan-von Neumann before signature/Clifford consumers.
- Authority packet surfaces stay fail-closed and do not stand in for the
  missing four-point/parallelogram theorem.

## Historical Validation Ring

These surfaces still matter for compile integrity, but should be read as
historical route/packet receipts rather than as canonical frontier surfaces.

### NS historical CKN-route ring

- `DASHI/Physics/Closure/ClaySprintSixtyFourNSSourceBudgetExhaustionCKNRouteReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtyFiveNSPressureReconstructionCKNContractReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtySixNSCKNRSweepCalibrationReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtySevenNSCKNLemmaTestLadderReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtySevenNSCKNUniformityAuditReceipt.agda`

### YM historical authority/acceptance ring

- `DASHI/Physics/Closure/YMSprint88TransferSpectralGapHardInputsReceipt.agda`
- `DASHI/Physics/Closure/YMSprint89ScopedAuthorityTransferSpectralGapReceipt.agda`
- `DASHI/Physics/Closure/YMSprint99ExternalAcceptanceTerminalBoundaryReceipt.agda`
- `DASHI/Physics/Closure/YMSprint126OSToWightmanRouteLedger.agda`
- `DASHI/Physics/Closure/YMSprint127FinalSubmissionReadinessLedger.agda`
- `DASHI/Physics/Closure/YMSprint127ClaySubmissionBoundaryLedger.agda`
