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

data NSKatoHessianConfinementShape : Set where
  hessianPSDAtTrueLambda2Core : NSKatoHessianConfinementShape
  positiveCrossDerivativeIsConfinementEvidence : NSKatoHessianConfinementShape
  negativeCrossDerivativeConfinementCorrectionRecorded : NSKatoHessianConfinementShape
  globalLocalMinimumAtTrueVortexCore : NSKatoHessianConfinementShape
  n128TwoPlaneHessianPositiveDefiniteRecorded : NSKatoHessianConfinementShape
  pressureHessianAdverseOnPositiveLaneRecorded : NSKatoHessianConfinementShape
  divergenceMachinePrecisionRecorded : NSKatoHessianConfinementShape

canonicalNSKatoHessianConfinementShape : List NSKatoHessianConfinementShape
canonicalNSKatoHessianConfinementShape =
  hessianPSDAtTrueLambda2Core
  ∷ positiveCrossDerivativeIsConfinementEvidence
  ∷ negativeCrossDerivativeConfinementCorrectionRecorded
  ∷ globalLocalMinimumAtTrueVortexCore
  ∷ n128TwoPlaneHessianPositiveDefiniteRecorded
  ∷ pressureHessianAdverseOnPositiveLaneRecorded
  ∷ divergenceMachinePrecisionRecorded
  ∷ []

data NSKatoHessianConfinementBlocker : Set where
  noMillerBridge :
    NSKatoHessianConfinementBlocker
  noExternalDNSPromotion :
    NSKatoHessianConfinementBlocker
  noFullRegularityInhabitant :
    NSKatoHessianConfinementBlocker
  noClayPromotion :
    NSKatoHessianConfinementBlocker

canonicalNSKatoHessianConfinementBlockers : List NSKatoHessianConfinementBlocker
canonicalNSKatoHessianConfinementBlockers =
  noMillerBridge
  ∷ noExternalDNSPromotion
  ∷ noFullRegularityInhabitant
  ∷ noClayPromotion
  ∷ []

shapeHessianPSDText : String
shapeHessianPSDText =
  "At a true global/local λ2 minimum, mixed-direction Hessian for λ2 is recorded as positive semidefinite by calculus."

shapeCrossDerivativePositiveText : String
shapeCrossDerivativePositiveText =
  "At the true λ2 minimum/vortex core, cross-derivative sign support is recorded as positive; this is the confinement signal."

shapeSignCorrectionText : String
shapeSignCorrectionText =
  "The prior negative-cross-derivative-as-confinement convention is corrected: positive cross-derivative supports confinement at the true core minimum."

shapePressureHessianText : String
shapePressureHessianText =
  "Pressure-Hessian local cross term is recorded as positive and adverse to confinement-sign promotion."

shapeTwoPlaneHessianText : String
shapeTwoPlaneHessianText =
  "N=128 true-core 2-plane Hessian block is recorded empirically as positive definite; this is a consistency datum only, not a theorem."

shapeDivergenceText : String
shapeDivergenceText =
  "Machine-precision divergence consistency is recorded as fail-closed empirical state."

record NSKatoHessianConfinementORCSLPGF : Set where
  constructor mkNSKatoHessianConfinementORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record a corrected λ2 Hessian/vortex-core confinement shape receipt at fail-closed posture."
    R : String
    RIsCanonical : R ≡
      "R: Record Hess(λ2) PSD-at-minimum, corrected positive cross-derivative confinement signal, pressure-Hessian adverse routing, and explicit blocker ledger."
    C : String
    CIsCanonical : C ≡
      "C: The receipt stores a typed canonical target/value shape and empirical N=128 row metadata only."
    S : String
    SIsCanonical : S ≡
      "S: Hessian PSD at core, positive cross-derivative as confinement evidence, negative-cross-derivative correction, pressure-Hessian adverse status, and divergence machine-precision recorded."
    L : String
    LIsCanonical : L ≡
      "L: Corrected sign convention at true λ2 minimum -> record empirical N=128 target row -> keep all promotions fail-closed."
    P : String
    PIsCanonical : P ≡
      "P: Do not promote any confinement theorem, external-DNS bridge, full regularity theorem, or Clay claim from this receipt."
    G : String
    GIsCanonical : G ≡
      "G: Governance guard: no Miller bridge, no external-DNS promotion path, no full-regularity inhabitant, no Clay promotion."
    F : String
    FIsCanonical : F ≡
      "F: Fail-closed due to explicit blockers and the corrected sign convention; proof obligations remain external to this row."

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

canonicalNSKatoHessianConfinementORCSLPGF :
  NSKatoHessianConfinementORCSLPGF
canonicalNSKatoHessianConfinementORCSLPGF =
  mkNSKatoHessianConfinementORCSLPGF
    "O: Record a corrected λ2 Hessian/vortex-core confinement shape receipt at fail-closed posture."
    refl
    "R: Record Hess(λ2) PSD-at-minimum, corrected positive cross-derivative confinement signal, pressure-Hessian adverse routing, and explicit blocker ledger."
    refl
    "C: The receipt stores a typed canonical target/value shape and empirical N=128 row metadata only."
    refl
    "S: Hessian PSD at core, positive cross-derivative as confinement evidence, negative-cross-derivative correction, pressure-Hessian adverse status, and divergence machine-precision recorded."
    refl
    "L: Corrected sign convention at true λ2 minimum -> record empirical N=128 target row -> keep all promotions fail-closed."
    refl
    "P: Do not promote any confinement theorem, external-DNS bridge, full regularity theorem, or Clay claim from this receipt."
    refl
    "G: Governance guard: no Miller bridge, no external-DNS promotion path, no full-regularity inhabitant, no Clay promotion."
    refl
    "F: Fail-closed due to explicit blockers and the corrected sign convention; proof obligations remain external to this row."
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
