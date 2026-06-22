# Architecture Notes for DashI Closure Path

## Reader Navigation

Use the repo through one canonical map and two reader tracks:

- entry surface: `README.md`
- repo structure guide: `Docs/RepoGuide.md`
- physics/unification guide: `Docs/PhysicsGuide.md`
- compressed claim surface: `Docs/UnificationClaim.md`
- origin traceability ledger: `Docs/OriginTraceabilityLedger.md`
- core-spine bridge: `Docs/CoreSpineBridge.md`
- ITIR/PNF residual bridge: `Docs/ITIRPNFResidualLogicBridge.md`
- boundary/example lane: `Docs/AntifascisticBoundaryAndMusic.md`
- music attractor target: `Docs/MusicalAttractorTheorem.md`
- strong theorem owners:
  `DASHI.Physics.Closure.UnifiedPhysicsTheorem`,
  `DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem`,
  `DASHI.Physics.Closure.PhysicsUnificationToCanonicalClosureAdapter`
- atom/wave secondary note: `Docs/AtomAndWaveRecoveryStatus.md`
- recovery truth surfaces: `Docs/PhysicsRecoveryLedger.md`, `Docs/ArchiveRecoveryCrosswalk.md`

Classification discipline for those surfaces:

- `proved`: current canonical theorem route and what it strictly establishes
- `bridge`: interpretation layers that connect formal and physics-facing statements
- `packaging`: assembly layers that bundle existing lanes without upgrading claims
- `empirical`: measurement/data lanes with explicit non-claim boundaries
- `speculative`: roadmap or intuition surfaces outside the current theorem contract

## Diagram Entry Points

The canonical textual diagram surfaces for this repo are:

- `Docs/RepoMetasystem.puml`
- `Docs/RepoMetasystem.svg`
- `Docs/diagrams/TaoQiPolarityMetasystem.puml`
- `Docs/CanonicalProofSpine.puml`
- `Docs/CanonicalProofSpine.svg`
- `Docs/PhysicsUnificationMap.puml`
- `Docs/PhysicsUnificationMap.svg`
- `Docs/PhysicsRealityRoadmap.puml`
- `Docs/PhysicsRealityRoadmap.svg`
- `Docs/ObservableSignatureGaugeEntryRound.puml`
- `Docs/ObservableSignatureGaugeEntryRound.svg`
- `Docs/TRAINING_DYNAMICS.puml`
- `Docs/TRAINING_DYNAMICS.svg`

Regenerate rendered SVG and PNG previews with:

```bash
./scripts/render_docs_diagrams.sh
```

Use them in this order:

1. `Docs/RepoMetasystem.*` for repo-level orientation
2. `Docs/diagrams/TaoQiPolarityMetasystem.puml` for the Tao -> symbol geometry -> yin/yang -> Qi -> phase/field interpretive stack
3. `Docs/CanonicalProofSpine.*` for the canonical theorem route
4. `Docs/OriginTraceabilityLedger.md` for origin/disconnection governance
5. `Docs/PhysicsUnificationMap.*` for claim boundaries and open gaps
6. `Docs/PhysicsRealityRoadmap.*` for "how this touches actual physics"
7. child graphs such as observable/signature and training-dynamics only after the first six

Diagram-reading rule:
the status boards in `RepoMetasystem`, `CanonicalProofSpine`,
`PhysicsUnificationMap`, and `PhysicsRealityRoadmap` are intentional. Green is
theorem-owned, yellow is bridge/advanced-but-blocked, blue is packaging,
red/pink is empirical or open-gate material. Do not recolor a box without a
named theorem owner or an explicit ledger update.

## Canonical Spine (Authoritative)
The canonical closure dependency spine is:

1. `DASHI.Geometry.ProjectionDefect`
2. `DASHI.Geometry.ProjectionDefectSplitForcesParallelogram`
3. `DASHI.Geometry.ProjectionDefectToParallelogram`
4. `DASHI.Geometry.QuadraticForm`
5. `DASHI.Physics.Closure.ContractionForcesQuadraticStrong`
6. `DASHI.Geometry.CausalForcesLorentz31`
7. `DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem`
8. `DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem`
9. `DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem`

This is the only required theorem route for quadratic and signature emergence.

## Strong Claim Owners

The strong repo-native physics-unification claim now lives in code first:

1. `DASHI.Physics.Closure.UnifiedPhysicsTheorem`
2. `DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem`
3. `DASHI.Physics.Closure.PhysicsUnificationToCanonicalClosureAdapter`

Read them in that order.

- `UnifiedPhysicsTheorem` is the main owner for the strong claim.
- `AtomicChemistryRecoveryTheorem` is the atom/chemistry interpretation carrier.
- `PhysicsUnificationToCanonicalClosureAdapter` is the explicit seam between
  abstract `UnifiedClosure.PhysicsUnification` and the canonical
  checklist/package/full-closure story.

## Route Classification Policy
- `canonical`: required for Stage C theorem closure claims.
- `alternative`: mathematically valid alternate derivation; not required.
- `validation`: independent cross-check used to reduce proof-risk.
- `experimental`: speculative or partial scaffolding not used for closure claims.

Modules currently in the quadratic family
(`QuadraticFromNorm`, `QuadraticFromProjection`, `QuadraticFromParallelogram`,
`QuadraticEmergence`, `QuadraticFormEmergence`) should be classified under this
policy and consumed accordingly.

## Remaining Architecture Work
1. Keep `ProjectionDefectToParallelogram` and
   `ContractionForcesQuadraticStrong` as the active canonical bottleneck bridge
   surfaces.
2. Replace any raw seam placeholders with named seam packages on canonical
   modules only.
3. Thread signature/Clifford/gauge recovery from canonical spine exports
   instead of parallel emergence routes.
4. Keep signature and Clifford routes logically separate:
   - signature route:
     `ContractionForcesQuadraticStrong -> ContractionQuadraticToSignatureBridgeTheorem`
   - Clifford route:
     `ContractionForcesQuadraticStrong -> QuadraticToCliffordBridgeTheorem`
     (canonical bilinear from normalized quadratic, then Clifford presentation).

## WaveLift⇒Even Architecture Rule (2026-03-11)
1. `Quadratic⇒Clifford` is the sole upstream producer for
   `WaveLift⇒Even` on the canonical path.
2. `WaveLift⇒Even` is a factorization theorem, not a predicate-only claim:
   `State → Cl` must factor through `EvenSubalgebra.incl`.
3. Add explicit Clifford grading interface (`parity`, closure on multiplication,
   unit-even witness) at the canonical Clifford bridge layer.
4. Define canonical wave lift using even Clifford words so image-evenness is by
   construction.
5. Keep this independent from full Dirac operator semantics at this stage.

Current status: implemented and validated with targeted checks on
`CliffordEvenLiftBridge`, `CliffordToEvenWaveLiftBridgeTheorem`,
`CanonicalContractionToCliffordBridgeTheorem`, and
`KnownLimitsQFTBridgeTheorem`.

## Tao/YinYang/Qi Interpretive Stack

The current cultural/interpretive stack is now explicitly layered as:

1. `DASHI.Culture.TaoChapterReadingReceipt`
2. `DASHI.Culture.TaoOperatorGrammar`
3. `DASHI.Culture.YinYangSymbolGeometryBoundary`
4. `DASHI.Culture.YinYangPolarityBoundary`
5. `DASHI.Interop.TaoYinYangAdapter`
6. `DASHI.Interop.YinYangQiAdapter`
7. `DASHI.Interop.PolarityPhaseFieldBridge`
8. `DASHI.Interop.PolarityBettiSupportBoundary`
9. `DASHI.Interop.BettiQiAdapter`
10. `DASHI.Interop.CarryCompletionSpectralBridge`
11. `DASHI.Interop.TaoQiReadingAdapter`
12. `DASHI.Interop.TaoMeditationQiAdapter`
13. `DASHI.Promotion.PolarityFieldObligationIndex`
14. `DASHI.Promotion.TaoQiObligationIndex`

Architecture rule for this stack:

- Tao supplies source-dependent motifs and chapter-local candidate readings.
- Yin-yang symbol geometry supplies the formulaic circle, eye, teardrop, region, and S-curve support surface for the polarity boundary.
- Yin/yang supplies the polarity and transition grammar between Tao operators and Qi formal-lens/operator surfaces.
- The carry/completion bridge preserves exact 3-adic, moonshine, quotient-seam, and Stage12 carry-depth receipts before any candidate-only cultural rereading is attached.
- The polarity-phase-field bridge is where local `TriTruth`/`HexTruth`/`NonaryTruth`, voxel/supervoxel support, and wave/superposition grammar sit.
- Betti support sits over that local support geometry as a candidate-only topology summary layer for connected components, loops, and voids before Qi interpretation.
- Qi remains the carrier/role/formal-lens substrate.
- Every layer is candidate-only and fail-closed on doctrine, empirical, clinical, spiritual, mystical, metaphysical, political, philological, theorem, runtime, and reciprocal validation authority.

## Performance Intent
Reducing parallel dependency paths lowers normalization and transport overhead.
Expected effect: lower compile pressure without changing theorem content.
