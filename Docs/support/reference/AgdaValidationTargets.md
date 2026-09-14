# Agda Validation Targets

Purpose: keep the validation manifest aligned with the live NS/YM/unification
frontiers and the current aggregate/focused-check policy.

Updated: `2026-09-13`

## Reading rule

This manifest distinguishes:

- current canonical frontiers;
- downstream consumer/compiler surfaces;
- historical route receipts that should still typecheck but are no longer the
  best statement of the live frontier;
- workflow wiring from observed commit-specific kernel receipts.

Current canonical reading:

- **NS:** `C_direct` is constructed; P3/same-output debt payment is the current
  local producer search; R568 is the live cutoff-uniform commutator-only
  spacetime producer; R572 and R503 are downstream compiler/consumer surfaces.
  A1-A9 remains a historical/alternative route.
- **Unification:** the live wall remains the current UCT/U-1a-H chain, with
  downstream consumers kept fail-closed.
- **YM:** the genuine missing-content burden remains the current
  Balaban-centered transfer/continuum authority cutset.

## Certification firewall

For every proof-critical owner record three separate facts:

```text
validation root exists?
workflow targets it?
observed commit-specific Agda success receipt?
```

A source module can be mathematically constructed without an observed current
CI receipt.  A workflow can target a root without having produced a successful
run for the commit under discussion.  Neither source prose nor CI wiring may be
promoted into a kernel receipt.

## Aggregate check policy

Preferred pinned focused runner:

```bash
nix develop .# --command \
  bash scripts/run_agda29_parallel_check.sh <module>.agda
```

The older direct smoke command remains useful when appropriate:

```bash
timeout 15s agda -i . <module>.agda
```

Aggregate integration surface:

```bash
agda -i . DASHI/Everything.agda
```

Interpretation:

- Exit `124` on a timeout-based targeted check means budget exceeded, not a
  type error.
- A targeted pass checks only the requested dependency closure.
- The aggregate check is a compile-integration signal; it does not change
  theorem-promotion flags.
- No successful result should be claimed without observing the corresponding
  command/run for the commit being described.

## Focused NS workflow

Canonical workflow:

```text
.github/workflows/ns-triad-concrete-retained-fiber-agda.yml
```

It performs, in order:

1. anti-hole/postulate checking via `scripts/check_ns_triad_clay_frontier.py`;
2. the exact signed finite laboratory;
3. completion-identity checks;
4. pinned Agda checks for selected cumulative proof-frontier roots;
5. after the Paper-1 migration, the canonical paper-interface validation root.

The workflow explicitly targets selected roots in R101-R132, then R185, R193,
R200, R201, and R202.  This is evidence of deliberate kernel-checkability of
that proof spine.  It is not by itself evidence that every historical PR head
received a successful run.

Canonical Paper-1 validation root:

```text
DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda
```

This root is intentionally fail-closed: it requires the direct companion and
compiler surfaces to remain constructed while R568, P3, same-output debt
payment, and Clay terminal promotion remain false until their authoritative
owners change.

## Canonical frontier targets

### NS wall: P3 same-output payment, then R568

Current paper/interface surface:

- `DASHI/Papers/NavierStokes/TheoremInterface.agda`
- `DASHI/Papers/NavierStokes/TheoremInterfaceValidation.agda`
- `Docs/papers/live/Paper1NavierStokesClayDraft.md`

Current local same-output frontier:

- `DASHI/Physics/Closure/NSTriadKNComparableFixedOutputCarrierRound207Exact.agda`
- `DASHI/Physics/Closure/NSTriadKNComparableOutputGramTelescopeRound209Exact.agda`
- `DASHI/Physics/Closure/NSTriadKNComparableOutputResidualPaymentRound211Exact.agda`
- `DASHI/Physics/Closure/NSTriadKNComparableConstantBandGramNoGoRound214Exact.agda`

Current modern direct chain:

- `DASHI/Physics/Closure/NSTriadKNDirectResolventIntegratedCompanionRound500Exact.agda`
- `DASHI/Physics/Closure/NSTriadKNDirectResolventSignedCrossToR415Round503Exact.agda`
- `DASHI/Physics/Closure/NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact.agda`
- `DASHI/Physics/Closure/NSTriadKNDirectLeafACompilerRound572Exact.agda`

Operational reading:

- `C_direct` / the integrated direct companion is constructed modulo the
  explicit standard integration authority already named by R500.
- R209 gives the exact same-output debt telescope; R211 is the existing payment
  socket.  The current P3 producer must pay that socket rather than introduce a
  parallel residual API.
- R214 is a negative control: fixed shell width/localization alone does not pay
  same-output Gram debt.
- R568 is the live novel cutoff-uniform PDE producer on the modern direct route.
- R572 compiles a paid R568 budget plus separated temporal/order receipts into
  the pre-existing R503 consumer surface.
- R503's R500-to-R415 compiler is closed, but its analytic direct-off-diagonal
  budget is not automatically paid.

Selected cumulative certification roots already wired in the focused workflow:

```text
R101 R102 R103 R104 R105 R106 R107 R108 R109 R110
R111 R112 R113 R114 R115 R117 R120 R121 R123
R126 R128 R130 R132
R185 R193 R200 R201 R202
```

The interval R133-R178 contains substantial theorem-bearing construction used
by later roots (helicity slots, normalized curl, homogeneity, quadratic kernel,
raw-curl weld, dual defect, low-output mass) but does not currently have the
same dense set of individually named workflow checkpoints.  Its certification
status should therefore be derived from actual transitive checked roots or
future dedicated receipts, not assumed from source existence alone.

### YM wall: transfer/continuum authority then no-spectral-pollution

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

- Mosco/liminf compactness is necessary but not itself the complete wall.
- Transfer/no-spectral-pollution and RP/OS/Wightman authority remain explicit
  fail-closed coordinates.
- Historical acceptance/readiness ledgers remain useful, but do not substitute
  for the current mathematical/authority cutset.

### Unification wall: U-1a-H through Jordan-von Neumann, then authority

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

- The live unification wall is not generic full unification.
- The first real theorem burden is the scale-invariant cross-term / U-1a-H
  route into cross-term nullity.
- Nullity must feed the actual four-point/parallelogram/Jordan-von Neumann
  chain before signature/Clifford consumers.
- Authority packet surfaces stay fail-closed.

## Promotion probes

Probe modules live under `DASHI/Physics/Probes/` and are intentionally not
imported by `DASHI/Everything.agda`.

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
- Probe modules are allowed to fail at the first strengthened root assertion
  not currently satisfied.
- Probes reduce the search space; they do not promote the theorem they probe.

## Historical validation ring

### NS historical A1-A9 / CKN / ESS route

Retain the old A1-A9 packet and CKN-route receipts for regression, provenance,
and alternative-strategy analysis.  They are not the canonical current NS
frontier after the 2026-09-13 Paper-1 migration.

Representative surfaces include:

- `DASHI/Physics/Closure/NSAbelTriadicDefectMeasureConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSAbelTriadicStationarityConstructionBoundary.agda`
- `DASHI/Physics/Closure/NSBoundedAbelMassEstimateBoundary.agda`
- `DASHI/Physics/Closure/NSQuantitativeStationarityRateBoundary.agda`
- `DASHI/Physics/Closure/NSLeiRenTianOutputSupportTransferBoundary.agda`
- `DASHI/Physics/Closure/NSA5KappaBiasVanishingFromA4StationarityBoundary.agda`
- `DASHI/Physics/Closure/NSPointwiseToAbelCompositeA6Boundary.agda`
- `DASHI/Physics/Closure/NSA7ResidualDepletionGronwallBoundary.agda`
- `DASHI/Physics/Closure/NSA8A9MonotonicityClosureTheoremLadderBoundary.agda`
- `DASHI/Physics/Closure/ClaySprintSixtyFourNSSourceBudgetExhaustionCKNRouteReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtyFiveNSPressureReconstructionCKNContractReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtySixNSCKNRSweepCalibrationReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtySevenNSCKNLemmaTestLadderReceipt.agda`
- `DASHI/Physics/Closure/ClaySprintSixtySevenNSCKNUniformityAuditReceipt.agda`

Historical interpretation:

- these were serious earlier theorem/reduction attempts;
- their unresolved coordinates remain historical facts;
- useful donor mathematics should be retained and attributed;
- their existence does not imply either failure or success of the modern direct
  route.

### YM historical authority/acceptance ring

- `DASHI/Physics/Closure/YMSprint88TransferSpectralGapHardInputsReceipt.agda`
- `DASHI/Physics/Closure/YMSprint89ScopedAuthorityTransferSpectralGapReceipt.agda`
- `DASHI/Physics/Closure/YMSprint99ExternalAcceptanceTerminalBoundaryReceipt.agda`
- `DASHI/Physics/Closure/YMSprint126OSToWightmanRouteLedger.agda`
- `DASHI/Physics/Closure/YMSprint127FinalSubmissionReadinessLedger.agda`
- `DASHI/Physics/Closure/YMSprint127ClaySubmissionBoundaryLedger.agda`
