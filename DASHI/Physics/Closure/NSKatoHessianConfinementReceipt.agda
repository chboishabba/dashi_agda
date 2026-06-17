module DASHI.Physics.Closure.NSKatoHessianConfinementReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Corrected Kato/Hessian confinement diagnostic receipt.
--
-- This is a strict fail-closed receipt for the corrected sign convention at a
-- true λ2 minimum / vortex-core target: Hess(λ2) should be positive
-- semidefinite; positive ∂e1∂e2 λ2 is confinement evidence, not adverse
-- evidence.  The N=128 target record is purely symbolic/typed and is
-- empirical-only.

data NSKatoHessianSign : Set where
  signNegative : NSKatoHessianSign
  signPositive : NSKatoHessianSign

data NSKatoHessianConfinementStatus : Set where
  failClosedShapeOnly : NSKatoHessianConfinementStatus

record NSKatoHessianEigenvalueProjection : Set where
  constructor mkNSKatoHessianEigenvalueProjection
  field
    eigenAxis : Nat
    eigenAxisLabel : String
    eigenvalue : String

record NSKatoHessianFullHessian3DProjection : Set where
  constructor mkNSKatoHessianFullHessian3DProjection
  field
    hessianCoreGeometryIsTriaxial : Bool
    hessianCoreGeometryIsTriaxialIsTrue :
      hessianCoreGeometryIsTriaxial ≡ true
    hessianCoreIsInfiniteTubeLike : Bool
    hessianCoreIsInfiniteTubeLikeIsFalse :
      hessianCoreIsInfiniteTubeLike ≡ false
    h33IsLarge : Bool
    h33IsLargeIsTrue :
      h33IsLarge ≡ true
    h33Eigenvalue : String
    h33EigenvalueIsCanonical :
      h33Eigenvalue ≡ "11754.22"
    fullHessianEigenvalues : List NSKatoHessianEigenvalueProjection

canonicalNSKatoHessianFullHessianEigenvalues :
  List NSKatoHessianEigenvalueProjection
canonicalNSKatoHessianFullHessianEigenvalues =
  mkNSKatoHessianEigenvalueProjection 1 "λ1" "1612.35"
  ∷ mkNSKatoHessianEigenvalueProjection 2 "λ2" "7131.77"
  ∷ mkNSKatoHessianEigenvalueProjection 3 "h33" "11754.22"
  ∷ []

canonicalNSKatoHessianFullHessian3DProjection :
  NSKatoHessianFullHessian3DProjection
canonicalNSKatoHessianFullHessian3DProjection =
  mkNSKatoHessianFullHessian3DProjection
    true
    refl
    false
    refl
    true
    refl
    "11754.22"
    refl
    canonicalNSKatoHessianFullHessianEigenvalues

data NSKatoHessianConfinementShape : Set where
  hessianPSDAtTrueLambda2Core : NSKatoHessianConfinementShape
  lambda2NegativeRegionShapeRecorded : NSKatoHessianConfinementShape
  positiveCrossDerivativeIsConfinementEvidence : NSKatoHessianConfinementShape
  negativeCrossDerivativeConfinementCorrectionRecorded : NSKatoHessianConfinementShape
  globalLocalMinimumAtTrueVortexCore : NSKatoHessianConfinementShape
  hessian3DCoreTriaxialRecorded : NSKatoHessianConfinementShape
  hessian3DFullEigenSpectrumRecorded : NSKatoHessianConfinementShape
  n128TwoPlaneHessianPositiveDefiniteRecorded : NSKatoHessianConfinementShape
  trueKatoStableFractionRecorded : NSKatoHessianConfinementShape
  kappaAbsGt1FractionRecorded : NSKatoHessianConfinementShape
  kappaSignedGt1FractionRecorded : NSKatoHessianConfinementShape
  pressureHessianAdverseOnPositiveLaneRecorded : NSKatoHessianConfinementShape
  pressureQcritRouteAdverseRecorded : NSKatoHessianConfinementShape
  katoTubeBoundaryTheoremCandidateOnlyRecorded : NSKatoHessianConfinementShape
  omegaTubeOmegaSheetSplitCorrectedRecorded : NSKatoHessianConfinementShape
  millerBridgeOpenTheoremCandidateOnlyRecorded : NSKatoHessianConfinementShape
  divergenceMachinePrecisionRecorded : NSKatoHessianConfinementShape

canonicalNSKatoHessianConfinementShape : List NSKatoHessianConfinementShape
canonicalNSKatoHessianConfinementShape =
  hessianPSDAtTrueLambda2Core
  ∷ lambda2NegativeRegionShapeRecorded
  ∷ positiveCrossDerivativeIsConfinementEvidence
  ∷ negativeCrossDerivativeConfinementCorrectionRecorded
  ∷ globalLocalMinimumAtTrueVortexCore
  ∷ hessian3DCoreTriaxialRecorded
  ∷ hessian3DFullEigenSpectrumRecorded
  ∷ n128TwoPlaneHessianPositiveDefiniteRecorded
  ∷ trueKatoStableFractionRecorded
  ∷ kappaAbsGt1FractionRecorded
  ∷ kappaSignedGt1FractionRecorded
  ∷ pressureHessianAdverseOnPositiveLaneRecorded
  ∷ pressureQcritRouteAdverseRecorded
  ∷ katoTubeBoundaryTheoremCandidateOnlyRecorded
  ∷ omegaTubeOmegaSheetSplitCorrectedRecorded
  ∷ millerBridgeOpenTheoremCandidateOnlyRecorded
  ∷ divergenceMachinePrecisionRecorded
  ∷ []

data NSKatoHessianConfinementBlocker : Set where
  millerBridgeOpenTheoremCandidateOnly :
    NSKatoHessianConfinementBlocker
  noExternalDNSPromotion :
    NSKatoHessianConfinementBlocker
  noFullRegularityInhabitant :
    NSKatoHessianConfinementBlocker
  noClayPromotion :
    NSKatoHessianConfinementBlocker

canonicalNSKatoHessianConfinementBlockers : List NSKatoHessianConfinementBlocker
canonicalNSKatoHessianConfinementBlockers =
  millerBridgeOpenTheoremCandidateOnly
  ∷ noExternalDNSPromotion
  ∷ noFullRegularityInhabitant
  ∷ noClayPromotion
  ∷ []

shapeHessianPSDText : String
shapeHessianPSDText =
  "At a true global/local λ2 minimum, mixed-direction Hessian for λ2 is recorded as positive semidefinite by calculus."

shapeLambda2NegativeRegionText : String
shapeLambda2NegativeRegionText =
  "λ2<0 region is recorded as the true Kato-sign region used in the N=128 aggregate receipt."

shapeCrossDerivativePositiveText : String
shapeCrossDerivativePositiveText =
  "At the true λ2 minimum/vortex core, cross-derivative sign support is recorded as positive; this is the confinement signal."

shapeSignCorrectionText : String
shapeSignCorrectionText =
  "The prior negative-cross-derivative-as-confinement convention is corrected: positive cross-derivative supports confinement at the true core minimum."

shapePressureHessianText : String
shapePressureHessianText =
  "Pressure-Hessian local cross term is recorded as positive and adverse to confinement-sign promotion."

shapeHessian3DGeometryText : String
shapeHessian3DGeometryText =
  "Core geometry is recorded as triaxial (not infinite-tube-like); h33 is large and 3D."

shapeFullHessianEigenvaluesText : String
shapeFullHessianEigenvaluesText =
  "Full 3D Hessian eigenvalues are recorded as [1612.35, 7131.77, 11754.22]."

shapeTwoPlaneHessianText : String
shapeTwoPlaneHessianText =
  "N=128 true-core 2-plane Hessian block is recorded empirically as positive definite; this is a consistency datum only, not a theorem."

shapeTrueKatoStableFractionText : String
shapeTrueKatoStableFractionText =
  "Aggregate N=128 true Kato stable fraction / cross-derivative-positive fraction is recorded at approximately 49.75%."

shapeKappaAbsGt1FractionText : String
shapeKappaAbsGt1FractionText =
  "Aggregate N=128 kappa_abs_gt_1 fraction is recorded at approximately 30.63%."

shapeKappaSignedGt1FractionText : String
shapeKappaSignedGt1FractionText =
  "Aggregate N=128 kappa_signed_gt_1 fraction is recorded at approximately 15.29%."

shapePressureQcritRouteAdverseText : String
shapePressureQcritRouteAdverseText =
  "Pressure/Qcrit route is recorded as adverse to confinement promotion and remains fail-closed."

shapeKatoTubeBoundaryCandidateText : String
shapeKatoTubeBoundaryCandidateText =
  "Kato tube boundary is recorded as theorem-candidate only, not a promoted theorem."

shapeOmegaTubeOmegaSheetSplitText : String
shapeOmegaTubeOmegaSheetSplitText =
  "Corrected Ωtube/Ωsheet split is recorded in the aggregate N=128 table; the split is empirical, typed, and not promoted."

shapeMillerBridgeOpenText : String
shapeMillerBridgeOpenText =
  "Miller bridge is recorded as open only as a theorem-candidate route; no promotion is claimed."

shapeDivergenceText : String
shapeDivergenceText =
  "Machine-precision divergence consistency is recorded as fail-closed empirical state."

record NSKatoHessianAggregateStats : Set where
  constructor mkNSKatoHessianAggregateStats
  field
    aggregateN : Nat
    aggregateNIs128 : aggregateN ≡ 128
    lambda2NegativeRegionRecorded : Bool
    lambda2NegativeRegionRecordedIsTrue : lambda2NegativeRegionRecorded ≡ true
    trueKatoStableFractionText : String
    trueKatoStableFractionTextIsCanonical :
      trueKatoStableFractionText ≡ shapeTrueKatoStableFractionText
    kappaAbsGt1FractionText : String
    kappaAbsGt1FractionTextIsCanonical :
      kappaAbsGt1FractionText ≡ shapeKappaAbsGt1FractionText
    kappaSignedGt1FractionText : String
    kappaSignedGt1FractionTextIsCanonical :
      kappaSignedGt1FractionText ≡ shapeKappaSignedGt1FractionText
    pressureQcritRouteAdverse : Bool
    pressureQcritRouteAdverseIsTrue : pressureQcritRouteAdverse ≡ true
    pressureQcritRouteAdverseText : String
    pressureQcritRouteAdverseTextIsCanonical :
      pressureQcritRouteAdverseText ≡ shapePressureQcritRouteAdverseText
    katoTubeBoundaryTheoremCandidateOnly : Bool
    katoTubeBoundaryTheoremCandidateOnlyIsTrue :
      katoTubeBoundaryTheoremCandidateOnly ≡ true
    katoTubeBoundaryTheoremCandidateOnlyText : String
    katoTubeBoundaryTheoremCandidateOnlyTextIsCanonical :
      katoTubeBoundaryTheoremCandidateOnlyText ≡ shapeKatoTubeBoundaryCandidateText
    omegaTubeOmegaSheetSplitText : String
    omegaTubeOmegaSheetSplitTextIsCanonical :
      omegaTubeOmegaSheetSplitText ≡ shapeOmegaTubeOmegaSheetSplitText
    millerBridgeOpen : Bool
    millerBridgeOpenIsTrue : millerBridgeOpen ≡ true
    millerBridgeOpenText : String
    millerBridgeOpenTextIsCanonical :
      millerBridgeOpenText ≡ shapeMillerBridgeOpenText
    aggregateRouteIsFailClosed : Bool
    aggregateRouteIsFailClosedIsTrue : aggregateRouteIsFailClosed ≡ true

canonicalNSKatoHessianAggregateStats : NSKatoHessianAggregateStats
canonicalNSKatoHessianAggregateStats =
  mkNSKatoHessianAggregateStats
    128
    refl
    true
    refl
    shapeTrueKatoStableFractionText
    refl
    shapeKappaAbsGt1FractionText
    refl
    shapeKappaSignedGt1FractionText
    refl
    true
    refl
    shapePressureQcritRouteAdverseText
    refl
    true
    refl
    shapeKatoTubeBoundaryCandidateText
    refl
    shapeOmegaTubeOmegaSheetSplitText
    refl
    true
    refl
    shapeMillerBridgeOpenText
    refl
    true
    refl

record NSKatoHessianConfinementORCSLPGF : Set where
  constructor mkNSKatoHessianConfinementORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record a corrected λ2 Hessian/vortex-core confinement shape receipt at fail-closed posture."
    R : String
    RIsCanonical : R ≡
      "R: Record Hess(λ2) PSD-at-minimum, corrected positive cross-derivative confinement signal, full 3D Hessian core geometry + eigen-spectrum, aggregate N=128 stats, and explicit fail-closed gate rows."
    C : String
    CIsCanonical : C ≡
      "C: The receipt stores typed canonical target/value shapes and empirical N=128 aggregate metadata only."
    S : String
    SIsCanonical : S ≡
      "S: Hessian PSD at core, λ2<0 region, triaxial full-3D core correction (large h33), positive cross-derivative confinement evidence, corrected Ωtube/Ωsheet split, and divergence machine-precision are recorded."
    L : String
    LIsCanonical : L ≡
      "L: Corrected sign convention at true λ2 minimum -> record empirical N=128 aggregate rows -> keep all promotions fail-closed."
    P : String
    PIsCanonical : P ≡
      "P: Do not promote any confinement theorem, external-DNS bridge, global regularity claim, full regularity theorem, or Clay claim from this receipt."
    G : String
    GIsCanonical : G ≡
      "G: Governance guard: Miller bridge open only as theorem-candidate, no external-DNS promotion path, no full/global regularity inhabitant, no Clay promotion."
    F : String
    FIsCanonical : F ≡
      "F: Fail-closed due to explicit gate rows and the corrected sign convention; proof obligations remain external to this row."

data NSKatoHessianConfinementPromotion : Set where

nSKatoHessianNoPromotion : NSKatoHessianConfinementPromotion → ⊥
nSKatoHessianNoPromotion ()

n128TargetCoordinates : List Nat
n128TargetCoordinates =
  35 ∷ 36 ∷ 99 ∷ []

record NSKatoHessianConfinementN128Target : Set where
  constructor mkNSKatoHessianConfinementN128Target
  field
    targetName : String
    targetCoordinates : List Nat
    targetCoordinatesIsCanonical : targetCoordinates ≡ n128TargetCoordinates
    lambda2SignAtTarget : NSKatoHessianSign
    lambda2SignAtTargetIsCanonical : lambda2SignAtTarget ≡ signNegative
    crossDerivativeSignAtTarget : NSKatoHessianSign
    crossDerivativeSignAtTargetIsCanonical : crossDerivativeSignAtTarget ≡ signPositive
    pressureHessianSignAtTarget : NSKatoHessianSign
    pressureHessianSignAtTargetIsCanonical : pressureHessianSignAtTarget ≡ signPositive
    pressureHessianIsAdverseToConfinement :
      Bool
    pressureHessianIsAdverseToConfinementIsTrue :
      pressureHessianIsAdverseToConfinement ≡ true
    divergenceMachinePrecision :
      String
    divergenceMachinePrecisionIsCanonical :
      divergenceMachinePrecision ≡ "machine_precision"
    routeIsConfinementEvidence :
      Bool
    routeIsConfinementEvidenceIsTrue :
      routeIsConfinementEvidence ≡ true

canonicalN128Target :
  NSKatoHessianConfinementN128Target
canonicalN128Target =
  mkNSKatoHessianConfinementN128Target
    "xV"
    n128TargetCoordinates
    refl
    signNegative
    refl
    signPositive
    refl
    signPositive
    refl
    true
    refl
    "machine_precision"
    refl
    true
    refl

record NSKatoHessianConfinementReceipt : Set where
  field
    status :
      NSKatoHessianConfinementStatus
    statusIsFailClosed :
      status ≡ failClosedShapeOnly
    shapeLedger :
      List NSKatoHessianConfinementShape
    shapeLedgerIsCanonical :
      shapeLedger ≡ canonicalNSKatoHessianConfinementShape
    hessianPSDRecorded :
      Bool
    hessianPSDRecordedIsTrue :
      hessianPSDRecorded ≡ true
    hessianPSDTextRecorded :
      String
    hessianPSDTextRecordedIsCanonical :
      hessianPSDTextRecorded ≡ shapeHessianPSDText
    hessian3DGeometryTextRecorded :
      String
    hessian3DGeometryTextRecordedIsCanonical :
      hessian3DGeometryTextRecorded ≡ shapeHessian3DGeometryText
    fullHessianEigenvaluesTextRecorded :
      String
    fullHessianEigenvaluesTextRecordedIsCanonical :
      fullHessianEigenvaluesTextRecorded ≡ shapeFullHessianEigenvaluesText
    lambda2NegativeRegionRecorded :
      Bool
    lambda2NegativeRegionRecordedIsTrue :
      lambda2NegativeRegionRecorded ≡ true
    lambda2NegativeRegionTextRecorded :
      String
    lambda2NegativeRegionTextRecordedIsCanonical :
      lambda2NegativeRegionTextRecorded ≡ shapeLambda2NegativeRegionText
    crossDerivativePositiveRecorded :
      Bool
    crossDerivativePositiveRecordedIsTrue :
      crossDerivativePositiveRecorded ≡ true
    crossDerivativePositiveTextRecorded :
      String
    crossDerivativePositiveTextRecordedIsCanonical :
      crossDerivativePositiveTextRecorded ≡ shapeCrossDerivativePositiveText
    signCorrectionRecorded :
      Bool
    signCorrectionRecordedIsTrue :
      signCorrectionRecorded ≡ true
    signCorrectionTextRecorded :
      String
    signCorrectionTextRecordedIsCanonical :
      signCorrectionTextRecorded ≡ shapeSignCorrectionText
    pressureHessianAdverseTextRecorded :
      String
    pressureHessianAdverseTextRecordedIsCanonical :
      pressureHessianAdverseTextRecorded ≡ shapePressureHessianText
    twoPlaneHessianPositiveDefiniteTextRecorded :
      String
    twoPlaneHessianPositiveDefiniteTextRecordedIsCanonical :
      twoPlaneHessianPositiveDefiniteTextRecorded ≡ shapeTwoPlaneHessianText
    fullHessian3DProjectionRecorded :
      NSKatoHessianFullHessian3DProjection
    fullHessian3DProjectionRecordedIsCanonical :
      fullHessian3DProjectionRecorded ≡ canonicalNSKatoHessianFullHessian3DProjection
    aggregateStats :
      NSKatoHessianAggregateStats
    aggregateStatsIsCanonical :
      aggregateStats ≡ canonicalNSKatoHessianAggregateStats
    divergenceTextRecorded :
      String
    divergenceTextRecordedIsCanonical :
      divergenceTextRecorded ≡ shapeDivergenceText
    divergenceRouteRecorded :
      Bool
    divergenceRouteRecordedIsTrue :
      divergenceRouteRecorded ≡ true
    blockers :
      List NSKatoHessianConfinementBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSKatoHessianConfinementBlockers
    target :
      NSKatoHessianConfinementN128Target
    targetIsCanonical :
      target ≡ canonicalN128Target
    millerBridgePromoted :
      Bool
    millerBridgePromotedIsFalse :
      millerBridgePromoted ≡ false
    externalDNSPromoted :
      Bool
    externalDNSPromotedIsFalse :
      externalDNSPromoted ≡ false
    fullRegularityPromoted :
      Bool
    fullRegularityPromotedIsFalse :
      fullRegularityPromoted ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    confinementClaimPromoted :
      Bool
    confinementClaimPromotedIsFalse :
      confinementClaimPromoted ≡ false
    orcslpgf :
      NSKatoHessianConfinementORCSLPGF

open NSKatoHessianConfinementORCSLPGF public
open NSKatoHessianEigenvalueProjection public
open NSKatoHessianFullHessian3DProjection public

canonicalNSKatoHessianConfinementORCSLPGF :
  NSKatoHessianConfinementORCSLPGF
canonicalNSKatoHessianConfinementORCSLPGF =
  mkNSKatoHessianConfinementORCSLPGF
    "O: Record a corrected λ2 Hessian/vortex-core confinement shape receipt at fail-closed posture."
    refl
    "R: Record Hess(λ2) PSD-at-minimum, corrected positive cross-derivative confinement signal, full 3D Hessian core geometry + eigen-spectrum, aggregate N=128 stats, and explicit fail-closed gate rows."
    refl
    "C: The receipt stores typed canonical target/value shapes and empirical N=128 aggregate metadata only."
    refl
    "S: Hessian PSD at core, λ2<0 region, triaxial full-3D core correction (large h33), positive cross-derivative confinement evidence, corrected Ωtube/Ωsheet split, and divergence machine-precision are recorded."
    refl
    "L: Corrected sign convention at true λ2 minimum -> record empirical N=128 aggregate rows -> keep all promotions fail-closed."
    refl
    "P: Do not promote any confinement theorem, external-DNS bridge, global regularity claim, full regularity theorem, or Clay claim from this receipt."
    refl
    "G: Governance guard: Miller bridge open only as theorem-candidate, no external-DNS promotion path, no full/global regularity inhabitant, no Clay promotion."
    refl
    "F: Fail-closed due to explicit gate rows and the corrected sign convention; proof obligations remain external to this row."
    refl

canonicalNSKatoHessianConfinementReceipt : NSKatoHessianConfinementReceipt
canonicalNSKatoHessianConfinementReceipt =
  record
    { status = failClosedShapeOnly
    ; statusIsFailClosed = refl
    ; shapeLedger = canonicalNSKatoHessianConfinementShape
    ; shapeLedgerIsCanonical = refl
    ; hessianPSDRecorded = true
    ; hessianPSDRecordedIsTrue = refl
    ; hessianPSDTextRecorded = shapeHessianPSDText
    ; hessianPSDTextRecordedIsCanonical = refl
    ; hessian3DGeometryTextRecorded = shapeHessian3DGeometryText
    ; hessian3DGeometryTextRecordedIsCanonical = refl
    ; fullHessianEigenvaluesTextRecorded = shapeFullHessianEigenvaluesText
    ; fullHessianEigenvaluesTextRecordedIsCanonical = refl
    ; lambda2NegativeRegionRecorded = true
    ; lambda2NegativeRegionRecordedIsTrue = refl
    ; lambda2NegativeRegionTextRecorded = shapeLambda2NegativeRegionText
    ; lambda2NegativeRegionTextRecordedIsCanonical = refl
    ; crossDerivativePositiveRecorded = true
    ; crossDerivativePositiveRecordedIsTrue = refl
    ; crossDerivativePositiveTextRecorded = shapeCrossDerivativePositiveText
    ; crossDerivativePositiveTextRecordedIsCanonical = refl
    ; signCorrectionRecorded = true
    ; signCorrectionRecordedIsTrue = refl
    ; signCorrectionTextRecorded = shapeSignCorrectionText
    ; signCorrectionTextRecordedIsCanonical = refl
    ; pressureHessianAdverseTextRecorded = shapePressureHessianText
    ; pressureHessianAdverseTextRecordedIsCanonical = refl
    ; twoPlaneHessianPositiveDefiniteTextRecorded = shapeTwoPlaneHessianText
    ; twoPlaneHessianPositiveDefiniteTextRecordedIsCanonical = refl
    ; fullHessian3DProjectionRecorded = canonicalNSKatoHessianFullHessian3DProjection
    ; fullHessian3DProjectionRecordedIsCanonical = refl
    ; aggregateStats = canonicalNSKatoHessianAggregateStats
    ; aggregateStatsIsCanonical = refl
    ; divergenceTextRecorded = shapeDivergenceText
    ; divergenceTextRecordedIsCanonical = refl
    ; divergenceRouteRecorded = true
    ; divergenceRouteRecordedIsTrue = refl
    ; blockers = canonicalNSKatoHessianConfinementBlockers
    ; blockersAreCanonical = refl
    ; target = canonicalN128Target
    ; targetIsCanonical = refl
    ; millerBridgePromoted = false
    ; millerBridgePromotedIsFalse = refl
    ; externalDNSPromoted = false
    ; externalDNSPromotedIsFalse = refl
    ; fullRegularityPromoted = false
    ; fullRegularityPromotedIsFalse = refl
    ; clayPromoted = false
    ; clayPromotedIsFalse = refl
    ; confinementClaimPromoted = false
    ; confinementClaimPromotedIsFalse = refl
    ; orcslpgf = canonicalNSKatoHessianConfinementORCSLPGF
    }

open NSKatoHessianConfinementReceipt public

------------------------------------------------------------------------
-- Kato-Morse theorem-by-theorem receipt surface (program prompt alignment).

data KatoMorseProofStatus : Set where
  provableClassical : KatoMorseProofStatus
  openBlocker : KatoMorseProofStatus

data KatoMorseTheorem : Set where
  MK1 : KatoMorseTheorem
  MK2 : KatoMorseTheorem
  MK3 : KatoMorseTheorem
  GD1 : KatoMorseTheorem
  GD2 : KatoMorseTheorem
  GD3 : KatoMorseTheorem
  theoremCConditional : KatoMorseTheorem

katoMorseTheoremName : KatoMorseTheorem → String
katoMorseTheoremName MK1 = "MK1"
katoMorseTheoremName MK2 = "MK2"
katoMorseTheoremName MK3 = "MK3"
katoMorseTheoremName GD1 = "GD1"
katoMorseTheoremName GD2 = "GD2"
katoMorseTheoremName GD3 = "GD3"
katoMorseTheoremName theoremCConditional = "Theorem C (conditional)"

katoMorseProofStatusName : KatoMorseProofStatus → String
katoMorseProofStatusName provableClassical = "provable classical"
katoMorseProofStatusName openBlocker = "open blocker"

record KatoMorseProgramVariables : Set where
  constructor mkKatoMorseProgramVariables
  field
    betaOfT : String
    OmegaBeta : String
    OmegaK : String
    g12 : String
    psi12 : String
    B : String
    c0 : String
    c1 : String
    H5 : String
    H6 : String

canonicalKatoMorseProgramVariables : KatoMorseProgramVariables
canonicalKatoMorseProgramVariables =
  mkKatoMorseProgramVariables
    "beta(t)=theta*lambda2min(t)"
    "OmegaBeta"
    "OmegaK"
    "g12"
    "B/g12"
    "B"
    "c0"
    "c1"
    "H5"
    "H6"

mk1Statement : String
mk1Statement =
  "MK1: geometric kernel preparation at beta(t)=theta*lambda2min(t), OmegaBeta, and OmegaK is available on a corrected-vortex-core branch."

mk2Statement : String
mk2Statement =
  "MK2: local Morse kernel counting step is recorded as provable classical under the Kato-Morse program bundle."

mk3Statement : String
mk3Statement =
  "MK3: minimum-split/shape coupling remains an unclosed route and is carried as a pending theorem-program target."

gd1Statement : String
gd1Statement =
  "GD1: gap-defect estimate is recorded with psi12=B/g12 as an open route on the existing Kato-Morse variables."

gd2Statement : String
gd2Statement =
  "GD2: geometric remainder transfer remains open and is not yet claim-closed."

gd3Statement : String
gd3Statement =
  "GD3: explicit correction: Hess λ2 L∞ is controlled by H5, while the Taylor confinement remainder requires H6."

theoremCConditionalStatement : String
theoremCConditionalStatement =
  "Theorem C (conditional): the final blow-up implication remains open until the exact curvature-to-Sobolev step through H6 is closed."

katoMorseTheoremStatement : KatoMorseTheorem → String
katoMorseTheoremStatement MK1 = mk1Statement
katoMorseTheoremStatement MK2 = mk2Statement
katoMorseTheoremStatement MK3 = mk3Statement
katoMorseTheoremStatement GD1 = gd1Statement
katoMorseTheoremStatement GD2 = gd2Statement
katoMorseTheoremStatement GD3 = gd3Statement
katoMorseTheoremStatement theoremCConditional = theoremCConditionalStatement

record KatoMorseProgramTheoremRow : Set where
  constructor mkKatoMorseProgramTheoremRow
  field
    theorem : KatoMorseTheorem
    theoremName : String
    theoremNameIsCanonical : theoremName ≡ katoMorseTheoremName theorem
    status : KatoMorseProofStatus
    statusText : String
    statusTextIsCanonical : statusText ≡ katoMorseProofStatusName status
    statement : String
    statementIsCanonical : statement ≡ katoMorseTheoremStatement theorem
    variables : KatoMorseProgramVariables
    variablesAreCanonical : variables ≡ canonicalKatoMorseProgramVariables

canonicalKatoMorseProgramRows : List KatoMorseProgramTheoremRow
canonicalKatoMorseProgramRows =
  mkKatoMorseProgramTheoremRow
    MK1
    (katoMorseTheoremName MK1)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    mk1Statement
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    MK2
    (katoMorseTheoremName MK2)
    refl
    provableClassical
    (katoMorseProofStatusName provableClassical)
    refl
    mk2Statement
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    MK3
    (katoMorseTheoremName MK3)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    mk3Statement
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    GD1
    (katoMorseTheoremName GD1)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    gd1Statement
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    GD2
    (katoMorseTheoremName GD2)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    gd2Statement
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    GD3
    (katoMorseTheoremName GD3)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    gd3Statement
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    theoremCConditional
    (katoMorseTheoremName theoremCConditional)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    theoremCConditionalStatement
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷ []

data KatoMorseProgramBlocker : Set where
  noProofOfTheoremCConditional : KatoMorseProgramBlocker
  noAcceptedCurvatureToSobolevTransfer : KatoMorseProgramBlocker
  noH5RequirementForHessianLInfinity : KatoMorseProgramBlocker
  noClayPromotion : KatoMorseProgramBlocker

canonicalKatoMorseProgramBlockers : List KatoMorseProgramBlocker
canonicalKatoMorseProgramBlockers =
  noProofOfTheoremCConditional
  ∷ noAcceptedCurvatureToSobolevTransfer
  ∷ noH5RequirementForHessianLInfinity
  ∷ noClayPromotion
  ∷ []

record KatoMorseProgramORCSLPGF : Set where
  constructor mkKatoMorseProgramORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record Kato-Morse theorem-by-theorem rows with explicit statuses and exact variable names."
    R : String
    RIsCanonical : R ≡
      "R: The prompt-aligned rows are MK1, MK2, MK3, GD1, GD2, GD3, and conditional Theorem C."
    C : String
    CIsCanonical : C ≡
      "C: Kato-Morse status fields are explicit as provable classical/open blocker."
    S : String
    SIsCanonical : S ≡
      "S: beta(t)=theta*lambda2min(t), OmegaBeta, OmegaK, g12, psi12=B/g12, B, c0, c1, H5, and H6 are recorded as exact program variables."
    L : String
    LIsCanonical : L ≡
      "L: theorem-by-theorem row surface feeds into the same confinement ledger as a typed program target, without changing existing exports."
    P : String
    PIsCanonical : P ≡
      "P: no Clay promotion is performed from this program surface."
    G : String
    GIsCanonical : G ≡
      "G: all pending route rows remain fail-closed; only typed record data is carried."
    F : String
    FIsCanonical : F ≡
      "F: status is explicit; theorem C remains open blocker; GD3 records the H5/H6 correction and remains open."

record KatoMorseProgramSurface : Set where
  constructor mkKatoMorseProgramSurface
  field
    theoremRows : List KatoMorseProgramTheoremRow
    theoremRowsAreCanonical : theoremRows ≡ canonicalKatoMorseProgramRows
    variableBundle : KatoMorseProgramVariables
    variableBundleIsCanonical : variableBundle ≡ canonicalKatoMorseProgramVariables
    curvatureToSobolevRow : String
    curvatureToSobolevRowIsCanonical : curvatureToSobolevRow ≡
      "The Hessian-vs-remainder correction is explicit: Hess λ2 L∞ requires H5, while Taylor confinement remainder needs H6."
    programBlockers : List KatoMorseProgramBlocker
    programBlockersAreCanonical : programBlockers ≡ canonicalKatoMorseProgramBlockers
    clayPromoted : Bool
    clayPromotedIsFalse : clayPromoted ≡ false
    theoremCOpen : Bool
    theoremCOpenIsTrue : theoremCOpen ≡ true
    programRecord : KatoMorseProgramORCSLPGF

canonicalKatoMorseProgramORCSLPGF : KatoMorseProgramORCSLPGF
canonicalKatoMorseProgramORCSLPGF =
  mkKatoMorseProgramORCSLPGF
    "O: Record Kato-Morse theorem-by-theorem rows with explicit statuses and exact variable names."
    refl
    "R: The prompt-aligned rows are MK1, MK2, MK3, GD1, GD2, GD3, and conditional Theorem C."
    refl
    "C: Kato-Morse status fields are explicit as provable classical/open blocker."
    refl
    "S: beta(t)=theta*lambda2min(t), OmegaBeta, OmegaK, g12, psi12=B/g12, B, c0, c1, H5, and H6 are recorded as exact program variables."
    refl
    "L: theorem-by-theorem row surface feeds into the same confinement ledger as a typed program target, without changing existing exports."
    refl
    "P: no Clay promotion is performed from this program surface."
    refl
    "G: all pending route rows remain fail-closed; only typed record data is carried."
    refl
    "F: status is explicit; theorem C remains open blocker; GD3 records the H5/H6 correction and remains open."
    refl

canonicalKatoMorseProgramSurface : KatoMorseProgramSurface
canonicalKatoMorseProgramSurface =
  mkKatoMorseProgramSurface
    canonicalKatoMorseProgramRows
    refl
    canonicalKatoMorseProgramVariables
    refl
    "The Hessian-vs-remainder correction is explicit: Hess λ2 L∞ requires H5, while Taylor confinement remainder needs H6."
    refl
    canonicalKatoMorseProgramBlockers
    refl
    false
    refl
    true
    refl
    canonicalKatoMorseProgramORCSLPGF
