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
  missingStressEnergyToCurvatureLaw :
    GRQFTConsumerMissingUpstreamField
  missingEinsteinEquationConsumer :
    GRQFTConsumerMissingUpstreamField
  missingSpinorGaugeRepresentationLaw :
    GRQFTConsumerMissingUpstreamField
  missingInteractionClosureLaw :
    GRQFTConsumerMissingUpstreamField
  missingEmpiricalGRQFTValidation :
    GRQFTConsumerMissingUpstreamField

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
    ; blockedFields =
        missingPromotionAuthorityToken
        ∷ missingStressEnergyToCurvatureLaw
        ∷ missingEinsteinEquationConsumer
        ∷ missingSpinorGaugeRepresentationLaw
        ∷ missingInteractionClosureLaw
        ∷ missingEmpiricalGRQFTValidation
        ∷ []
    ; requiredNextReceipt =
        "provide external authority plus GR equation and QFT interaction consumer laws before downstream closure promotion"
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
        ∷ "No Einstein equation recovery theorem is promoted here"
        ∷ "No QFT interaction-closure theorem is promoted here"
        ∷ "No empirical GR/QFT validation claim is made here"
        ∷ []
    }

canonicalGRQFTConsumerBlockedFields :
  List GRQFTConsumerMissingUpstreamField
canonicalGRQFTConsumerBlockedFields =
  GRQFTConsumerNextObligationCurrentStatus.blockedFields
    canonicalGRQFTConsumerNextObligationCurrentStatus
