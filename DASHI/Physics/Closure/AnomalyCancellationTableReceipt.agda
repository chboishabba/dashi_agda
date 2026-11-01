module DASHI.Physics.Closure.AnomalyCancellationTableReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt as HAnomaly
import DASHI.Physics.QFT.U1YFromConductorReceipt as U1Y

------------------------------------------------------------------------
-- Anomaly cancellation table receipt.
--
-- Standard Model anomaly cancellation is inherited conditionally: the
-- carrier must first match the Standard Model hypercharge assignment.

data AnomalyCancellationTableStatus : Set where
  anomalyCancellationInheritanceConditionRecorded :
    AnomalyCancellationTableStatus

data AnomalyCancellationEntry : Set where
  su3SquaredU1Y :
    AnomalyCancellationEntry

  su2SquaredU1Y :
    AnomalyCancellationEntry

  u1YCubed :
    AnomalyCancellationEntry

  gravitationalSquaredU1Y :
    AnomalyCancellationEntry

canonicalAnomalyCancellationEntries :
  List AnomalyCancellationEntry
canonicalAnomalyCancellationEntries =
  su3SquaredU1Y
  ∷ su2SquaredU1Y
  ∷ u1YCubed
  ∷ gravitationalSquaredU1Y
  ∷ []

data AnomalyCancellationBlocker : Set where
  smHyperchargeAssignmentInheritedButNotPromoted :
    AnomalyCancellationBlocker

  missingCarrierFermionRepresentationExhaustion :
    AnomalyCancellationBlocker

  missingAcceptedAnomalyAuthorityBinding :
    AnomalyCancellationBlocker

canonicalAnomalyCancellationBlockers :
  List AnomalyCancellationBlocker
canonicalAnomalyCancellationBlockers =
  smHyperchargeAssignmentInheritedButNotPromoted
  ∷ missingCarrierFermionRepresentationExhaustion
  ∷ missingAcceptedAnomalyAuthorityBinding
  ∷ []

data AnomalyCancellationPromotion : Set where

anomalyCancellationPromotionImpossibleHere :
  AnomalyCancellationPromotion →
  ⊥
anomalyCancellationPromotionImpossibleHere ()

inheritanceConditionLabel : String
inheritanceConditionLabel =
  "SM signed-sixth hypercharge assignment is inherited from the p3 Z/6 candidate for this table check"

record AnomalyCancellationTableReceipt : Setω where
  field
    status :
      AnomalyCancellationTableStatus

    matterSurfaceStatus :
      Matter.MatterRepresentationSurfaceStatus

    matterSurfaceStatusIsTargetsOnly :
      matterSurfaceStatus
      ≡
      Matter.matterRepresentationTargetsOnlyNoPromotion

    u1yReceipt :
      U1Y.U1YFromConductorReceipt

    z6HyperchargeCandidateRecorded :
      U1Y.u1yChargesAsZ6Characters u1yReceipt ≡ true

    hyperchargeAnomalyReceipt :
      HAnomaly.HyperchargeNormalisationAnomalyReceipt

    anomalyReceiptUsesZ6Unit :
      HAnomaly.carrierExplainsUnitOneSixth hyperchargeAnomalyReceipt
      ≡
      true

    inheritanceCondition :
      String

    inheritanceConditionIsCanonical :
      inheritanceCondition ≡ inheritanceConditionLabel

    anomalyEntries :
      List AnomalyCancellationEntry

    anomalyEntriesAreCanonical :
      anomalyEntries ≡ canonicalAnomalyCancellationEntries

    carrierChargesMatchSMHypercharge :
      Bool

    carrierChargesMatchSMHyperchargeIsTrue :
      carrierChargesMatchSMHypercharge ≡ true

    smHyperchargeAssignmentInheritedFromZ6Candidate :
      Bool

    smHyperchargeAssignmentInheritedFromZ6CandidateIsTrue :
      smHyperchargeAssignmentInheritedFromZ6Candidate ≡ true

    inheritedIfCarrierChargesMatchSMHypercharge :
      Bool

    inheritedIfCarrierChargesMatchSMHyperchargeIsTrue :
      inheritedIfCarrierChargesMatchSMHypercharge ≡ true

    cubicAnomalyCancels :
      Bool

    cubicAnomalyCancelsIsTrue :
      cubicAnomalyCancels ≡ true

    gravitationalAnomalyCancels :
      Bool

    gravitationalAnomalyCancelsIsTrue :
      gravitationalAnomalyCancels ≡ true

    su2MixedAnomalyCancels :
      Bool

    su2MixedAnomalyCancelsIsTrue :
      su2MixedAnomalyCancels ≡ true

    su3MixedAnomalyCancels :
      Bool

    su3MixedAnomalyCancelsIsTrue :
      su3MixedAnomalyCancels ≡ true

    anomalyCancellationPromoted :
      Bool

    anomalyCancellationPromotedIsFalse :
      anomalyCancellationPromoted ≡ false

    physicalGaugeMatterPromoted :
      Bool

    physicalGaugeMatterPromotedIsFalse :
      physicalGaugeMatterPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List AnomalyCancellationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalAnomalyCancellationBlockers

    promotionFlags :
      List AnomalyCancellationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open AnomalyCancellationTableReceipt public

canonicalAnomalyCancellationTableReceipt :
  AnomalyCancellationTableReceipt
canonicalAnomalyCancellationTableReceipt =
  record
    { status =
        anomalyCancellationInheritanceConditionRecorded
    ; matterSurfaceStatus =
        Matter.matterRepresentationTargetsOnlyNoPromotion
    ; matterSurfaceStatusIsTargetsOnly =
        refl
    ; u1yReceipt =
        U1Y.canonicalU1YFromConductorReceipt
    ; z6HyperchargeCandidateRecorded =
        refl
    ; hyperchargeAnomalyReceipt =
        HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; anomalyReceiptUsesZ6Unit =
        refl
    ; inheritanceCondition =
        inheritanceConditionLabel
    ; inheritanceConditionIsCanonical =
        refl
    ; anomalyEntries =
        canonicalAnomalyCancellationEntries
    ; anomalyEntriesAreCanonical =
        refl
    ; carrierChargesMatchSMHypercharge =
        true
    ; carrierChargesMatchSMHyperchargeIsTrue =
        refl
    ; smHyperchargeAssignmentInheritedFromZ6Candidate =
        true
    ; smHyperchargeAssignmentInheritedFromZ6CandidateIsTrue =
        refl
    ; inheritedIfCarrierChargesMatchSMHypercharge =
        true
    ; inheritedIfCarrierChargesMatchSMHyperchargeIsTrue =
        refl
    ; cubicAnomalyCancels =
        true
    ; cubicAnomalyCancelsIsTrue =
        HAnomaly.cubicAnomalyCancelsIsTrue
          HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; gravitationalAnomalyCancels =
        true
    ; gravitationalAnomalyCancelsIsTrue =
        HAnomaly.gravitationalAnomalyCancelsIsTrue
          HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; su2MixedAnomalyCancels =
        true
    ; su2MixedAnomalyCancelsIsTrue =
        HAnomaly.su2MixedAnomalyCancelsIsTrue
          HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; su3MixedAnomalyCancels =
        true
    ; su3MixedAnomalyCancelsIsTrue =
        HAnomaly.su3MixedAnomalyCancelsIsTrue
          HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; anomalyCancellationPromoted =
        false
    ; anomalyCancellationPromotedIsFalse =
        refl
    ; physicalGaugeMatterPromoted =
        false
    ; physicalGaugeMatterPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalAnomalyCancellationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The anomaly table records SU3^2-U1Y, SU2^2-U1Y, U1Y^3, and gravitational^2-U1Y checks"
        ∷ "The SM signed-sixth hypercharge table is inherited from the p3 Z/6 candidate for this table check"
        ∷ "The inherited table cancels all four recorded anomalies"
        ∷ "The table check does not promote physical gauge matter, physical CKM, or an exact Standard Model reconstruction"
        ∷ []
    }

anomalyCancellationTableDoesNotPromoteCKM :
  physicalCKMPromoted canonicalAnomalyCancellationTableReceipt ≡ false
anomalyCancellationTableDoesNotPromoteCKM =
  refl
