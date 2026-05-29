module DASHI.Physics.Closure.PenguinDecayCarrierDerivedC9ConstraintTargetReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierDerived as CKM
import DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt as Ratios
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.PenguinDecayC9C10P5PrimePredictionTargetReceipt as P5Target
import DASHI.Physics.Closure.PenguinDecayWilsonCoefficientAuthority as Wilson
import DASHI.Physics.Closure.YukawaFromCarrier as Yukawa

------------------------------------------------------------------------
-- Carrier-derived C9 constraint target.
--
-- This module records the next computation target for the P5'/C9 lane:
-- consume the current carrier CKM and Yukawa surfaces, then ask whether a
-- carrier-side loop computation can produce the right sign and scale for a
-- C9 new-physics shift.  It deliberately does not construct a numerical C9
-- value, Wilson-authority token, empirical residual, or anomaly claim.

data CarrierDerivedC9ConstraintTargetStatus : Set where
  carrierDerivedC9ConstraintTargetRecordedFailClosed :
    CarrierDerivedC9ConstraintTargetStatus

data CarrierDerivedC9ConstraintRole : Set where
  carrierLoopC9NPShiftSignAndMagnitudeTarget :
    CarrierDerivedC9ConstraintRole

data CarrierDerivedC9ConstraintBlocker : Set where
  missingEffectiveHamiltonianConvention :
    CarrierDerivedC9ConstraintBlocker

  missingLoopFunctionFromCarrierData :
    CarrierDerivedC9ConstraintBlocker

  missingFormFactorAndRGMatchingFromCarrierData :
    CarrierDerivedC9ConstraintBlocker

  missingPhysicalYukawaPromotion :
    CarrierDerivedC9ConstraintBlocker

  missingAcceptedWilsonAuthorityDigest :
    CarrierDerivedC9ConstraintBlocker

  missingSelectedRun12P5PrimeValueCovarianceAndResidualArtifacts :
    CarrierDerivedC9ConstraintBlocker

  missingFreezeAndNoPosteriorTuningAuthority :
    CarrierDerivedC9ConstraintBlocker

canonicalCarrierDerivedC9ConstraintBlockers :
  List CarrierDerivedC9ConstraintBlocker
canonicalCarrierDerivedC9ConstraintBlockers =
  missingEffectiveHamiltonianConvention
  ∷ missingLoopFunctionFromCarrierData
  ∷ missingFormFactorAndRGMatchingFromCarrierData
  ∷ missingPhysicalYukawaPromotion
  ∷ missingAcceptedWilsonAuthorityDigest
  ∷ missingSelectedRun12P5PrimeValueCovarianceAndResidualArtifacts
  ∷ missingFreezeAndNoPosteriorTuningAuthority
  ∷ []

data AcceptedCarrierDerivedC9ConstraintClaim : Set where

acceptedCarrierDerivedC9ConstraintClaimImpossibleHere :
  AcceptedCarrierDerivedC9ConstraintClaim →
  ⊥
acceptedCarrierDerivedC9ConstraintClaimImpossibleHere ()

record PenguinDecayCarrierDerivedC9ConstraintTargetReceipt : Setω where
  field
    status :
      CarrierDerivedC9ConstraintTargetStatus

    targetRole :
      CarrierDerivedC9ConstraintRole

    targetLabel :
      String

    targetLabelIsCanonical :
      targetLabel
      ≡
      "carrier-derived C9_NP sign and magnitude constraint target"

    targetNumericalScale :
      String

    targetNumericalScaleIsCanonical :
      targetNumericalScale
      ≡
      "target question: can carrier data produce C9_NP approximately -1 without posterior tuning?"

    ckmCarrierDerivedReceipt :
      CKM.CKMCarrierDerivedReceipt

    ckmCarrierDerivedReceiptThreadedFromCanonical :
      Bool

    ckmCarrierDerivedReceiptThreadedFromCanonicalIsTrue :
      ckmCarrierDerivedReceiptThreadedFromCanonical ≡ true

    ckmCarrierMatrix :
      Matter.MixingMatrix

    ckmCarrierMatrixIsCarrierDerived :
      ckmCarrierMatrix ≡ CKM.ckmCarrierMatrix ckmCarrierDerivedReceipt

    ckmCarrierMatrixIsIdentityAtCurrentFrontier :
      ckmCarrierMatrix ≡ Matter.identityMixingMatrix

    yukawaFromCarrierReceipt :
      Yukawa.YukawaFromCarrierReceipt

    yukawaFromCarrierReceiptThreadedFromCanonical :
      Bool

    yukawaFromCarrierReceiptThreadedFromCanonicalIsTrue :
      yukawaFromCarrierReceiptThreadedFromCanonical ≡ true

    carrierYukawaRatioTargetReceipt :
      Ratios.CarrierYukawaRatioTargetReceipt

    carrierYukawaRatioTargetReceiptThreadedFromCanonical :
      Bool

    carrierYukawaRatioTargetReceiptThreadedFromCanonicalIsTrue :
      carrierYukawaRatioTargetReceiptThreadedFromCanonical ≡ true

    physicalYukawaPromotionConstructed :
      Ratios.physicalRatioPredictionsPromoted
        carrierYukawaRatioTargetReceipt
      ≡
      false

    c9C10WilsonAuthorityDigest :
      Wilson.C9C10WilsonAuthorityDigest

    c9C10WilsonAuthorityDigestIsCanonical :
      c9C10WilsonAuthorityDigest
      ≡
      Wilson.canonicalC9C10WilsonAuthorityDigest

    wilsonDigestStillRequired :
      Wilson.authorityDigest c9C10WilsonAuthorityDigest
      ≡
      "required: sha256 digest of accepted C9/C10 Wilson coefficient authority artifact"

    p5PrimeTargetReceipt :
      P5Target.C9C10P5PrimePredictionTargetReceipt

    p5PrimeTargetReceiptThreadedFromCanonical :
      Bool

    p5PrimeTargetReceiptThreadedFromCanonicalIsTrue :
      p5PrimeTargetReceiptThreadedFromCanonical ≡ true

    p5PrimeTargetConstructed :
      P5Target.predictionTargetConstructed p5PrimeTargetReceipt
      ≡
      true

    p5PrimePromotionNotConstructed :
      P5Target.promotionConstructedHere p5PrimeTargetReceipt
      ≡
      false

    p5PrimeRun12PublicResultRecorded :
      Bool

    p5PrimeRun12PublicResultRecordedIsTrue :
      p5PrimeRun12PublicResultRecorded
      ≡
      true

    p5PrimeClaimed160745PrimaryRejected :
      Bool

    p5PrimeClaimed160745PrimaryRejectedIsTrue :
      p5PrimeClaimed160745PrimaryRejected
      ≡
      true

    p5PrimeFallbackIns1798504RouteRecorded :
      Bool

    p5PrimeFallbackIns1798504RouteRecordedIsTrue :
      p5PrimeFallbackIns1798504RouteRecorded
      ≡
      true

    carrierConstraintTargetRecorded :
      Bool

    carrierConstraintTargetRecordedIsTrue :
      carrierConstraintTargetRecorded ≡ true

    physicalC9ValueDerived :
      Bool

    physicalC9ValueDerivedIsFalse :
      physicalC9ValueDerived ≡ false

    wilsonAuthorityAccepted :
      Bool

    wilsonAuthorityAcceptedIsFalse :
      wilsonAuthorityAccepted ≡ false

    empiricalConstraintPromoted :
      Bool

    empiricalConstraintPromotedIsFalse :
      empiricalConstraintPromoted ≡ false

    acceptedAnomalyClaimConstructedHere :
      Bool

    acceptedAnomalyClaimConstructedHereIsFalse :
      acceptedAnomalyClaimConstructedHere ≡ false

    acceptedConstraintClaimBlocked :
      AcceptedCarrierDerivedC9ConstraintClaim →
      ⊥

    blockers :
      List CarrierDerivedC9ConstraintBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCarrierDerivedC9ConstraintBlockers

    receiptBoundary :
      List String

open PenguinDecayCarrierDerivedC9ConstraintTargetReceipt public

canonicalPenguinDecayCarrierDerivedC9ConstraintTargetReceipt :
  PenguinDecayCarrierDerivedC9ConstraintTargetReceipt
canonicalPenguinDecayCarrierDerivedC9ConstraintTargetReceipt =
  record
    { status =
        carrierDerivedC9ConstraintTargetRecordedFailClosed
    ; targetRole =
        carrierLoopC9NPShiftSignAndMagnitudeTarget
    ; targetLabel =
        "carrier-derived C9_NP sign and magnitude constraint target"
    ; targetLabelIsCanonical =
        refl
    ; targetNumericalScale =
        "target question: can carrier data produce C9_NP approximately -1 without posterior tuning?"
    ; targetNumericalScaleIsCanonical =
        refl
    ; ckmCarrierDerivedReceipt =
        CKM.canonicalCKMCarrierDerived
    ; ckmCarrierDerivedReceiptThreadedFromCanonical =
        true
    ; ckmCarrierDerivedReceiptThreadedFromCanonicalIsTrue =
        refl
    ; ckmCarrierMatrix =
        CKM.ckmCarrierMatrix CKM.canonicalCKMCarrierDerived
    ; ckmCarrierMatrixIsCarrierDerived =
        refl
    ; ckmCarrierMatrixIsIdentityAtCurrentFrontier =
        refl
    ; yukawaFromCarrierReceipt =
        Yukawa.canonicalYukawaFromCarrier
    ; yukawaFromCarrierReceiptThreadedFromCanonical =
        true
    ; yukawaFromCarrierReceiptThreadedFromCanonicalIsTrue =
        refl
    ; carrierYukawaRatioTargetReceipt =
        Ratios.canonicalCarrierYukawaRatioTargetReceipt
    ; carrierYukawaRatioTargetReceiptThreadedFromCanonical =
        true
    ; carrierYukawaRatioTargetReceiptThreadedFromCanonicalIsTrue =
        refl
    ; physicalYukawaPromotionConstructed =
        refl
    ; c9C10WilsonAuthorityDigest =
        Wilson.canonicalC9C10WilsonAuthorityDigest
    ; c9C10WilsonAuthorityDigestIsCanonical =
        refl
    ; wilsonDigestStillRequired =
        refl
    ; p5PrimeTargetReceipt =
        P5Target.canonicalC9C10P5PrimePredictionTargetReceipt
    ; p5PrimeTargetReceiptThreadedFromCanonical =
        true
    ; p5PrimeTargetReceiptThreadedFromCanonicalIsTrue =
        refl
    ; p5PrimeTargetConstructed =
        refl
    ; p5PrimePromotionNotConstructed =
        refl
    ; p5PrimeRun12PublicResultRecorded =
        true
    ; p5PrimeRun12PublicResultRecordedIsTrue =
        refl
    ; p5PrimeClaimed160745PrimaryRejected =
        true
    ; p5PrimeClaimed160745PrimaryRejectedIsTrue =
        refl
    ; p5PrimeFallbackIns1798504RouteRecorded =
        true
    ; p5PrimeFallbackIns1798504RouteRecordedIsTrue =
        refl
    ; carrierConstraintTargetRecorded =
        true
    ; carrierConstraintTargetRecordedIsTrue =
        refl
    ; physicalC9ValueDerived =
        false
    ; physicalC9ValueDerivedIsFalse =
        refl
    ; wilsonAuthorityAccepted =
        false
    ; wilsonAuthorityAcceptedIsFalse =
        refl
    ; empiricalConstraintPromoted =
        false
    ; empiricalConstraintPromotedIsFalse =
        refl
    ; acceptedAnomalyClaimConstructedHere =
        false
    ; acceptedAnomalyClaimConstructedHereIsFalse =
        refl
    ; acceptedConstraintClaimBlocked =
        acceptedCarrierDerivedC9ConstraintClaimImpossibleHere
    ; blockers =
        canonicalCarrierDerivedC9ConstraintBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The C9 constraint target consumes the current carrier CKM and Yukawa surfaces"
        ∷ "At the current frontier the carrier CKM is the identity matrix, so a physical C9 shift is not derived here"
        ∷ "The 2025 full Run 1+2 LHCb P5'/A_FB public result is recorded as the current target; HEPData 160745 is rejected here as b-jet mass, and HEPData:ins1798504 is fallback-only"
        ∷ "The Wilson digest, effective-Hamiltonian convention, loop/RG/form-factor matching, selected P5' value/covariance/residual artifacts, and clean freeze remain required"
        ∷ "No numerical C9_NP value, accepted anomaly claim, or empirical promotion is constructed"
        ∷ []
    }

canonicalCarrierDerivedC9ConstraintNoPromotion :
  empiricalConstraintPromoted
    canonicalPenguinDecayCarrierDerivedC9ConstraintTargetReceipt
  ≡
  false
canonicalCarrierDerivedC9ConstraintNoPromotion =
  refl
