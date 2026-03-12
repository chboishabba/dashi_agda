# Physics Closure Implementation Checklist

Date: 2026-03-12
Mode: `get-shit-done` planning pass

## Canonical Chain To Enforce

`ContractionForcesQuadraticTheorem`
→ `ContractionQuadraticToSignatureBridgeTheorem`
→ `ContractionSignatureToSpinDiracBridgeTheorem`
→ `PhysicsClosureFull`

## Execution Order (Concrete File Targets)

1. [x] `DASHI/Geometry/ProjectionDefectSplitForcesParallelogram.agda`
  - Keep this as the local engine for split/parallelogram forcing.
  - Mandatory theorem surface:
    - `projectionDefectSplitForcesParallelogram`
    - `projectionDefectOrthogonalAdditivity`
    - `projectionDefectEnergySplit`
    - `quadraticEmergenceFromProjectionDefectSplit`
    - `projectionDefectParallelogramFromSplit`
2. [x] `DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`
  - Centralize all strong transport/uniqueness logic.
  - Mandatory theorem surface:
    - `UniqueUpToScaleSeam`
    - `QuadraticUniquenessBridge`
    - `ContractionForcesQuadraticStrong`
    - `uniqueUpToScaleWitness`
3. [x] `DASHI/Physics/Closure/ContractionForcesQuadraticTheorem.agda`
  - Keep this as canonical entrypoint from contraction to quadratic theorem output.
  - Mandatory theorem surface:
    - `ContractionForcesQuadraticTheorem`
    - `fromStrongContraction`
    - `canonicalRealStackContractionForcesQuadraticTheorem`
4. [x] `DASHI/Physics/ConeArrowIsotropyForcesProfile.agda`
  - Keep as profile-selection front door only.
  - Mandatory theorem surface:
    - `ConeArrowIsotropyForcesProfile`
    - `measured≡forced`
5. [x] `DASHI/Physics/ConeArrowIsotropyForcesProfileShiftInstance.agda`
  - Keep the concrete shift witness pipeline here.
  - Mandatory theorem surface:
    - `shiftForcesProfile`
6. [x] `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
  - Force signature as theorem output (not choice field).
  - Mandatory theorem surface:
    - `ContractionQuadraticToSignatureBridgeTheorem`
    - `signatureForced31`
    - `normalizedQuadratic`
7. [x] Orbit-profile substrate files
  - `DASHI/Physics/OrbitProfileExternal.agda`
  - `DASHI/Physics/OrbitSignatureDiscriminant.agda`
  - `DASHI/Physics/ConeArrowIsotropyOrbitProfileAgreement.agda`
  - Ensure one canonical profile pipeline for signature discrimination.
8. [x] `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
  - Keep canonical `Quadratic⇒Clifford` route unique.
  - Mandatory theorem surface:
    - `quadraticToBilinear`
    - `CliffordPresentation`
    - `Quadratic⇒Clifford`
    - `QuadraticToCliffordBridgeTheorem`
9. [x] `DASHI/Physics/DecimationToClifford.agda`
  - Replace interface-only `rel : Set` and factorization placeholders with concrete laws.
  - Mandatory theorem surface:
    - `CliffordRelations.rel` becomes relation law family
    - `UniversalClifford` gains explicit factorization theorem
    - `decimation⇒clifford` proves actual hypotheses transfer
10. [x] `DASHI/Physics/Closure/ContractionSignatureToSpinDiracBridgeTheorem.agda`
  - Keep this as single signature-to-spin/Dirac bridge on canonical path.
11. [x] Wave evenness lock (mapped modules)
  - `DASHI/Physics/CliffordEvenLiftBridge.agda`
  - `DASHI/Physics/Closure/CliffordToEvenWaveLiftBridgeTheorem.agda`
  - Mandatory theorem surface:
    - `WaveLiftIntoEven`
    - `WaveLift⇒Even`
    - `canonicalWaveLiftIntoEvenFromContractionQuadratic`
12. [x] `DASHI/Physics/Closure/PhysicsClosureFull.agda`
  - Convert supplied fields to theorem-derived fields where possible:
    - contraction/quadratic
    - signature `(3,1)`
    - Clifford/spin/Dirac bridge package
13. [x] Closure instance + constraint closure files
  - `DASHI/Physics/Closure/PhysicsClosureInstanceAssumed.agda`
  - `DASHI/Algebra/ConstraintAlgebraClosure.agda`
  - `DASHI/Physics/Closure/ConstraintClosureFromCanonicalPathTheorem.agda`
  - Remove assumption-first seams from canonical route.
14. [x] Canonical exports + law surface
  - `DASHI/Physics/Closure/CanonicalStageC.agda`
  - `DASHI/Physics/AxiomSet.agda` (`AxiomLaws` record section)
  - `DASHI/Everything.agda`
  - Ensure canonical route is obvious and default-imported.

## Definition Of Done

- Canonical contraction output has unique/canonical quadratic witness.
- Canonical quadratic output forces Lorentz signature theorem (`sig31`).
- Canonical quadratic/signature package induces canonical Clifford and spin/Dirac bridge.
- Physical wave lift is theorem-level even (`WaveLiftIntoEven` witness form).
- `PhysicsClosureFull` is assembled primarily from theorem chain outputs.
- Constraint closure is derived/transported from canonical geometry package.
- Canonical path has no essential postulates left.
