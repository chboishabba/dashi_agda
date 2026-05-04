module DASHI.Physics.Closure.GRQFTConsumerNextObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem as GR
import DASHI.Physics.Closure.KnownLimitsInterpretableObservableConsumer as IOC
import DASHI.Physics.Closure.KnownLimitsQFTBridgeTheorem as QFT
import DASHI.Physics.Closure.KnownLimitsStatus as KLS

------------------------------------------------------------------------
-- W5n GR/QFT next-obligation surface.
--
-- The known-limits bridge modules already provide theorem-backed GR-like and
-- QFT-like local recovery surfaces.  This module deliberately does not turn
-- those surfaces into full downstream GR/QFT closure.  It only records the
-- next richer consumer fields, plus a typed diagnostic for the missing
-- upstream authority needed before such a promotion is admissible.

data GRQFTClosurePromotionAuthorityToken : Set where

record GRQFTDownstreamConsumerFields : Setω where
  field
    knownLimitsObservableConsumer :
      IOC.KnownLimitsInterpretableObservableConsumer

    grBridge :
      GR.KnownLimitsGRBridgeTheorem

    qftBridge :
      QFT.KnownLimitsQFTBridgeTheorem

    spacetimeCarrier : Set
    stressEnergyCarrier : Set
    curvatureCarrier : Set
    einsteinEquationCarrier : Set

    waveStateCarrier : Set
    spinorCarrier : Set
    gaugeRepresentationCarrier : Set
    interactionClosureCarrier : Set

    stressEnergyMap :
      spacetimeCarrier →
      stressEnergyCarrier

    curvatureMap :
      spacetimeCarrier →
      curvatureCarrier

    einsteinEquationConsumer :
      stressEnergyCarrier →
      curvatureCarrier →
      einsteinEquationCarrier

    spinorRealizationMap :
      waveStateCarrier →
      spinorCarrier

    gaugeRepresentationMap :
      spinorCarrier →
      gaugeRepresentationCarrier

    interactionClosureConsumer :
      gaugeRepresentationCarrier →
      interactionClosureCarrier

    grLikeStatus :
      KLS.KnownLimitsStatus.grLike KLS.canonicalKnownLimitsStatus
      ≡
      KLS.grLikeTheoremBacked

    qftLikeStatus :
      KLS.KnownLimitsStatus.qftLike KLS.canonicalKnownLimitsStatus
      ≡
      KLS.qftLikeTheoremBacked

    noPromotionBoundary :
      List String

record GRQFTClosurePromotionReceipt : Setω where
  field
    promotionAuthority :
      GRQFTClosurePromotionAuthorityToken

    downstreamConsumerFields :
      GRQFTDownstreamConsumerFields

    grEquationLaw :
      GRQFTDownstreamConsumerFields.einsteinEquationCarrier
        downstreamConsumerFields →
      Set

    qftInteractionLaw :
      GRQFTDownstreamConsumerFields.interactionClosureCarrier
        downstreamConsumerFields →
      Set

    grEquationLawAtConsumer :
      (stressEnergy :
        GRQFTDownstreamConsumerFields.stressEnergyCarrier
          downstreamConsumerFields) →
      (curvature :
        GRQFTDownstreamConsumerFields.curvatureCarrier
          downstreamConsumerFields) →
      grEquationLaw
        (GRQFTDownstreamConsumerFields.einsteinEquationConsumer
          downstreamConsumerFields
          stressEnergy
          curvature)

    qftInteractionLawAtConsumer :
      (waveState :
        GRQFTDownstreamConsumerFields.waveStateCarrier
          downstreamConsumerFields) →
      qftInteractionLaw
        (GRQFTDownstreamConsumerFields.interactionClosureConsumer
          downstreamConsumerFields
          (GRQFTDownstreamConsumerFields.gaugeRepresentationMap
            downstreamConsumerFields
            (GRQFTDownstreamConsumerFields.spinorRealizationMap
              downstreamConsumerFields
              waveState)))

------------------------------------------------------------------------
-- Current non-promoting diagnostic.

data GRQFTConsumerMissingUpstreamField : Set where
  missingPromotionAuthorityToken :
    GRQFTConsumerMissingUpstreamField
  missingPDFCarrierPrerequisite :
    GRQFTConsumerMissingUpstreamField
  missingGREquationLaw :
    GRQFTConsumerMissingUpstreamField
  missingGREquationLawAtConsumer :
    GRQFTConsumerMissingUpstreamField
  missingQFTInteractionLaw :
    GRQFTConsumerMissingUpstreamField
  missingQFTInteractionLawAtConsumer :
    GRQFTConsumerMissingUpstreamField
  missingEmpiricalGRQFTValidation :
    GRQFTConsumerMissingUpstreamField

data GRQFTPDFCarrierPrerequisiteStatus : Set where
  pdfCarrierPrerequisiteMissing :
    GRQFTPDFCarrierPrerequisiteStatus

record GRQFTPDFCarrierPrerequisiteDiagnostic : Set where
  field
    prerequisiteStatus :
      GRQFTPDFCarrierPrerequisiteStatus

    requiredCarrier :
      String

    sourceScanBoundary :
      List String

    noPDFCarrierConstructedHere :
      List String

canonicalGRQFTPDFCarrierPrerequisiteDiagnostic :
  GRQFTPDFCarrierPrerequisiteDiagnostic
canonicalGRQFTPDFCarrierPrerequisiteDiagnostic =
  record
    { prerequisiteStatus =
        pdfCarrierPrerequisiteMissing
    ; requiredCarrier =
        "external PDF carrier/mass-kernel route needed before W5 GR/QFT closure-promotion receipt can be assessed"
    ; sourceScanBoundary =
        "Current W5 sources do not provide an external PDF carrier"
        ∷ "Below-Z t43 comparison evidence explicitly records no external PDF"
        ∷ "Known-limits GR/QFT bridges do not derive the high-mass PDF carrier prerequisite"
        ∷ []
    ; noPDFCarrierConstructedHere =
        "This module does not construct a PDF carrier"
        ∷ "This module does not derive the neutral-current mass-kernel/PDF route"
        ∷ "This module does not use t43 numeric evidence as a W5 PDF prerequisite receipt"
        ∷ []
    }

record GRQFTClosurePromotionReceiptMissingFields : Set where
  field
    missingAuthority :
      GRQFTConsumerMissingUpstreamField

    missingPDFCarrier :
      GRQFTConsumerMissingUpstreamField

    missingGRLaw :
      GRQFTConsumerMissingUpstreamField

    missingGRConsumerLaw :
      GRQFTConsumerMissingUpstreamField

    missingQFTLaw :
      GRQFTConsumerMissingUpstreamField

    missingQFTConsumerLaw :
      GRQFTConsumerMissingUpstreamField

    missingEmpiricalValidation :
      GRQFTConsumerMissingUpstreamField

    receiptFieldDiagnostic :
      List String

canonicalGRQFTClosurePromotionReceiptMissingFields :
  GRQFTClosurePromotionReceiptMissingFields
canonicalGRQFTClosurePromotionReceiptMissingFields =
  record
    { missingAuthority =
        missingPromotionAuthorityToken
    ; missingPDFCarrier =
        missingPDFCarrierPrerequisite
    ; missingGRLaw =
        missingGREquationLaw
    ; missingGRConsumerLaw =
        missingGREquationLawAtConsumer
    ; missingQFTLaw =
        missingQFTInteractionLaw
    ; missingQFTConsumerLaw =
        missingQFTInteractionLawAtConsumer
    ; missingEmpiricalValidation =
        missingEmpiricalGRQFTValidation
    ; receiptFieldDiagnostic =
        "GRQFTClosurePromotionReceipt requires an external promotionAuthority"
        ∷ "GRQFTClosurePromotionReceipt requires the external PDF carrier prerequisite before W5 GR/QFT/PDF closure intake"
        ∷ "GRQFTClosurePromotionReceipt requires grEquationLaw"
        ∷ "GRQFTClosurePromotionReceipt requires grEquationLawAtConsumer"
        ∷ "GRQFTClosurePromotionReceipt requires qftInteractionLaw"
        ∷ "GRQFTClosurePromotionReceipt requires qftInteractionLawAtConsumer"
        ∷ "Downstream promotion also requires empirical GR/QFT validation outside known-limits recovery"
        ∷ []
    }

record GRQFTConsumerNextObligationCurrentStatus : Setω where
  field
    knownLimitsObservableConsumer :
      IOC.KnownLimitsInterpretableObservableConsumer

    grBridge :
      GR.KnownLimitsGRBridgeTheorem

    qftBridge :
      QFT.KnownLimitsQFTBridgeTheorem

    grKnownLimitsStatus :
      KLS.GRLikeStatus

    qftKnownLimitsStatus :
      KLS.QFTLikeStatus

    receiptMissingFields :
      GRQFTClosurePromotionReceiptMissingFields

    pdfCarrierPrerequisite :
      GRQFTPDFCarrierPrerequisiteDiagnostic

    blockedFields :
      List GRQFTConsumerMissingUpstreamField

    requiredNextReceipt :
      String

    knownLimitsBoundary :
      String

    closurePromotionBoundary :
      String

    noAuthorityConstructedHere :
      List String

    noPromotionBoundary :
      List String

canonicalGRQFTConsumerNextObligationCurrentStatus :
  GRQFTConsumerNextObligationCurrentStatus
canonicalGRQFTConsumerNextObligationCurrentStatus =
  record
    { knownLimitsObservableConsumer =
        IOC.canonicalKnownLimitsInterpretableObservableConsumer
    ; grBridge =
        GR.canonicalKnownLimitsGRBridgeTheorem
    ; qftBridge =
        QFT.canonicalKnownLimitsQFTBridgeTheorem
    ; grKnownLimitsStatus =
        KLS.KnownLimitsStatus.grLike KLS.canonicalKnownLimitsStatus
    ; qftKnownLimitsStatus =
        KLS.KnownLimitsStatus.qftLike KLS.canonicalKnownLimitsStatus
    ; receiptMissingFields =
        canonicalGRQFTClosurePromotionReceiptMissingFields
    ; pdfCarrierPrerequisite =
        canonicalGRQFTPDFCarrierPrerequisiteDiagnostic
    ; blockedFields =
        missingPromotionAuthorityToken
        ∷ missingPDFCarrierPrerequisite
        ∷ missingGREquationLaw
        ∷ missingGREquationLawAtConsumer
        ∷ missingQFTInteractionLaw
        ∷ missingQFTInteractionLawAtConsumer
        ∷ missingEmpiricalGRQFTValidation
        ∷ []
    ; requiredNextReceipt =
        "provide external authority, PDF carrier prerequisite, GR equation law, QFT interaction law, consumer law witnesses, and empirical GR/QFT validation before downstream closure promotion"
    ; knownLimitsBoundary =
        "known-limits GR/QFT bridges are theorem-backed local recovery surfaces, not full GR/QFT closure"
    ; closurePromotionBoundary =
        "GRQFTClosurePromotionAuthorityToken has no constructor in this module"
    ; noAuthorityConstructedHere =
        "This module does not construct GRQFTClosurePromotionAuthorityToken"
        ∷ "This module does not inhabit GRQFTClosurePromotionReceipt"
        ∷ []
    ; noPromotionBoundary =
        "This module is a W5 next-obligation surface only"
        ∷ "No GR equation law or consumer proof is promoted here"
        ∷ "No QFT interaction law or consumer proof is promoted here"
        ∷ "No empirical GR/QFT validation claim is made here"
        ∷ []
    }

canonicalGRQFTConsumerBlockedFields :
  List GRQFTConsumerMissingUpstreamField
canonicalGRQFTConsumerBlockedFields =
  GRQFTConsumerNextObligationCurrentStatus.blockedFields
    canonicalGRQFTConsumerNextObligationCurrentStatus

canonicalGRQFTConsumerReceiptMissingFields :
  GRQFTClosurePromotionReceiptMissingFields
canonicalGRQFTConsumerReceiptMissingFields =
  GRQFTConsumerNextObligationCurrentStatus.receiptMissingFields
    canonicalGRQFTConsumerNextObligationCurrentStatus
