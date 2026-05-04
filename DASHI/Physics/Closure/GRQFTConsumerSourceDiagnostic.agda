module DASHI.Physics.Closure.GRQFTConsumerSourceDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GRQFTConsumerNextObligation as W5

------------------------------------------------------------------------
-- W5 current-source diagnostic.
--
-- This module scans the existing W5 next-obligation surface.  It records
-- source availability for the receipt fields without constructing promotion
-- authority, GR/QFT laws, consumer witnesses, empirical validation, or the
-- downstream closure-promotion receipt.

data GRQFTConsumerSourceAvailability : Set where
  sourcePresent :
    GRQFTConsumerSourceAvailability
  sourceMissing :
    GRQFTConsumerSourceAvailability

record GRQFTConsumerReceiptSourceAvailability : Set where
  field
    promotionAuthoritySource :
      GRQFTConsumerSourceAvailability

    pdfCarrierPrerequisiteSource :
      GRQFTConsumerSourceAvailability

    grEquationLawSource :
      GRQFTConsumerSourceAvailability

    grEquationLawWitnessSource :
      GRQFTConsumerSourceAvailability

    qftInteractionLawSource :
      GRQFTConsumerSourceAvailability

    qftInteractionLawWitnessSource :
      GRQFTConsumerSourceAvailability

    downstreamConsumerFieldsSource :
      GRQFTConsumerSourceAvailability

    knownLimitsObservableConsumerSource :
      GRQFTConsumerSourceAvailability

    grBridgeSource :
      GRQFTConsumerSourceAvailability

    qftBridgeSource :
      GRQFTConsumerSourceAvailability

    empiricalValidationSource :
      GRQFTConsumerSourceAvailability

canonicalGRQFTConsumerReceiptSourceAvailability :
  GRQFTConsumerReceiptSourceAvailability
canonicalGRQFTConsumerReceiptSourceAvailability =
  record
    { promotionAuthoritySource =
        sourceMissing
    ; pdfCarrierPrerequisiteSource =
        sourceMissing
    ; grEquationLawSource =
        sourceMissing
    ; grEquationLawWitnessSource =
        sourceMissing
    ; qftInteractionLawSource =
        sourceMissing
    ; qftInteractionLawWitnessSource =
        sourceMissing
    ; downstreamConsumerFieldsSource =
        sourceMissing
    ; knownLimitsObservableConsumerSource =
        sourcePresent
    ; grBridgeSource =
        sourcePresent
    ; qftBridgeSource =
        sourcePresent
    ; empiricalValidationSource =
        sourceMissing
    }

grqftPromotionAuthorityImpossibleHere :
  W5.GRQFTClosurePromotionAuthorityToken →
  ⊥
grqftPromotionAuthorityImpossibleHere ()

grqftPromotionReceiptImpossibleHere :
  W5.GRQFTClosurePromotionReceipt →
  ⊥
grqftPromotionReceiptImpossibleHere receipt =
  grqftPromotionAuthorityImpossibleHere
    (W5.GRQFTClosurePromotionReceipt.promotionAuthority receipt)

record GRQFTConsumerSourceDiagnostic : Setω where
  field
    nextObligationStatus :
      W5.GRQFTConsumerNextObligationCurrentStatus

    receiptMissingFields :
      W5.GRQFTClosurePromotionReceiptMissingFields

    pdfCarrierPrerequisite :
      W5.GRQFTPDFCarrierPrerequisiteDiagnostic

    receiptBlockedFields :
      List W5.GRQFTConsumerMissingUpstreamField

    blockedFieldsStillCanonical :
      receiptBlockedFields
      ≡
      W5.canonicalGRQFTConsumerBlockedFields

    sourceAvailability :
      GRQFTConsumerReceiptSourceAvailability

    knownLimitsBoundary :
      String

    closurePromotionBoundary :
      String

    requiredNextReceipt :
      String

    diagnosticBoundary :
      List String

    blockerImpact :
      List String

    impossibleAuthorityHere :
      W5.GRQFTClosurePromotionAuthorityToken →
      ⊥

    impossibleReceiptHere :
      W5.GRQFTClosurePromotionReceipt →
      ⊥

canonicalGRQFTConsumerSourceDiagnostic :
  GRQFTConsumerSourceDiagnostic
canonicalGRQFTConsumerSourceDiagnostic =
  record
    { nextObligationStatus =
        W5.canonicalGRQFTConsumerNextObligationCurrentStatus
    ; receiptMissingFields =
        W5.canonicalGRQFTConsumerReceiptMissingFields
    ; pdfCarrierPrerequisite =
        W5.canonicalGRQFTPDFCarrierPrerequisiteDiagnostic
    ; receiptBlockedFields =
        W5.canonicalGRQFTConsumerBlockedFields
    ; blockedFieldsStillCanonical =
        refl
    ; sourceAvailability =
        canonicalGRQFTConsumerReceiptSourceAvailability
    ; knownLimitsBoundary =
        W5.GRQFTConsumerNextObligationCurrentStatus.knownLimitsBoundary
          W5.canonicalGRQFTConsumerNextObligationCurrentStatus
    ; closurePromotionBoundary =
        W5.GRQFTConsumerNextObligationCurrentStatus.closurePromotionBoundary
          W5.canonicalGRQFTConsumerNextObligationCurrentStatus
    ; requiredNextReceipt =
        W5.GRQFTConsumerNextObligationCurrentStatus.requiredNextReceipt
          W5.canonicalGRQFTConsumerNextObligationCurrentStatus
    ; diagnosticBoundary =
        "Current W5 source scan imports only GRQFTConsumerNextObligation"
        ∷ "Known-limits observable consumer, GR bridge, and QFT bridge sources are present"
        ∷ "Complete GRQFTDownstreamConsumerFields source is not promoted here"
        ∷ "No external PDF carrier prerequisite source is present for W5 GR/QFT/PDF closure intake"
        ∷ "No promotion authority, GR equation law, QFT interaction law, or consumer law witness source is present"
        ∷ "No empirical GR/QFT validation source is present"
        ∷ []
    ; blockerImpact =
        "Strict blocker remains: W5 cannot promote known-limits GR/QFT recovery into GR/QFT closure"
        ∷ "The next admissible step is still an external GRQFTClosurePromotionReceipt with authority, PDF carrier prerequisite, laws, witnesses, downstream fields, and empirical validation"
        ∷ "This diagnostic fabricates no authority token, PDF carrier, empirical validation token, or promotion receipt"
        ∷ []
    ; impossibleAuthorityHere =
        grqftPromotionAuthorityImpossibleHere
    ; impossibleReceiptHere =
        grqftPromotionReceiptImpossibleHere
    }
