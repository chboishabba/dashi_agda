module DASHI.Analysis.RiemannG2GammaLineageHighestAlphaReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GammaProducerSourceAcquisitionExact as Acquisition
import DASHI.Analysis.RiemannG2GammaCandidateSourceLineageRecoveryExact as Candidate

------------------------------------------------------------------------
-- POST-RECOVERY GAMMA BIDI CUT
--
-- The vendored companion source now settles the historical identity question:
--
--   PoleQuotientGammaBudget.exists_gamma_budget_linear_in_stripConst
--     -> LiteralWeilGammaConeBound.gammaConeEnvelope.
--
-- Thus the epsGamma/gammaConeEnvelope chain IS the reported pole-quotient Gamma
-- producer at source level.  Its own source also identifies the coarse scaling
-- mechanism: stripConst contains the sample-test second-derivative L1 norm,
-- which grows quadratically as the taper support shrinks.
--
-- The historical repair route therefore begins at the localized strip/C2 norm
-- estimate.  A fresh theorem-bearing same-g_pole proof remains an equally valid
-- alternative final-consumer route.
------------------------------------------------------------------------

data GammaHighestAlphaPayment : Set where
  discoverAnyConcreteGammaSourceFamily : GammaHighestAlphaPayment
  recoverEpsGammaEnvelopeLineage : GammaHighestAlphaPayment
  proveLineageIs8889PoleQuotientProducer : GammaHighestAlphaPayment
  recoverAlternate8889ProducerIfNot : GammaHighestAlphaPayment
  localizeFirstLossBeforeConsumerIdentity : GammaHighestAlphaPayment
  localizeFirstLossAfterConsumerIdentity : GammaHighestAlphaPayment
  repairIdentifiedLoss : GammaHighestAlphaPayment


data PaymentState : Set where
  pruned : PaymentState
  owned : PaymentState
  live : PaymentState
  blocked : PaymentState
  downstream : PaymentState

paymentState : GammaHighestAlphaPayment → PaymentState
paymentState discoverAnyConcreteGammaSourceFamily = pruned
paymentState recoverEpsGammaEnvelopeLineage = owned
paymentState proveLineageIs8889PoleQuotientProducer = owned
paymentState recoverAlternate8889ProducerIfNot = pruned
paymentState localizeFirstLossBeforeConsumerIdentity = pruned
paymentState localizeFirstLossAfterConsumerIdentity = owned
paymentState repairIdentifiedLoss = live

concreteSourceDiscoveryPruned :
  paymentState discoverAnyConcreteGammaSourceFamily ≡ pruned
concreteSourceDiscoveryPruned = refl

candidateLineageOwned :
  paymentState recoverEpsGammaEnvelopeLineage ≡ owned
candidateLineageOwned = refl

sameConsumerIdentityOwned :
  paymentState proveLineageIs8889PoleQuotientProducer ≡ owned
sameConsumerIdentityOwned = refl

localizedHistoricalLossOwned :
  paymentState localizeFirstLossAfterConsumerIdentity ≡ owned
localizedHistoricalLossOwned = refl

repairLocalizedHistoricalLossLive :
  paymentState repairIdentifiedLoss ≡ live
repairLocalizedHistoricalLossLive = refl

candidateOwnerAgreesSourceFamilyRecovered :
  Candidate.concreteGammaSourceFamilyRecovered
    Candidate.canonicalGammaCandidateLineageBoundary ≡ true
candidateOwnerAgreesSourceFamilyRecovered =
  Candidate.concreteGammaSourceFamilyRecoveredIsTrue
    Candidate.canonicalGammaCandidateLineageBoundary

candidateOwnerAgreesConsumerIdentityRecovered :
  Candidate.exact8889ConsumerIdentityRecovered
    Candidate.canonicalGammaCandidateLineageBoundary ≡ true
candidateOwnerAgreesConsumerIdentityRecovered =
  Candidate.exact8889ConsumerIdentityRecoveredIsTrue
    Candidate.canonicalGammaCandidateLineageBoundary

record GammaLineageHighestAlphaBoundary : Set where
  constructor gamma-lineage-highest-alpha-boundary
  field
    genericProducerArtifactSearchStillFirstLeaf : Bool
    genericProducerArtifactSearchStillFirstLeafIsFalse :
      genericProducerArtifactSearchStillFirstLeaf ≡ false

    concreteEpsGammaEnvelopeFamilyRecovered : Bool
    concreteEpsGammaEnvelopeFamilyRecoveredIsTrue :
      concreteEpsGammaEnvelopeFamilyRecovered ≡ true

    sameConsumer8889ProvenanceStillRequired : Bool
    sameConsumer8889ProvenanceStillRequiredIsFalse :
      sameConsumer8889ProvenanceStillRequired ≡ false

    sourcePrecisionLossLocalizationRecovered : Bool
    sourcePrecisionLossLocalizationRecoveredIsTrue :
      sourcePrecisionLossLocalizationRecovered ≡ true

    sourceFreeStirlingOrDigammaGuessAdmissible : Bool
    sourceFreeStirlingOrDigammaGuessAdmissibleIsFalse :
      sourceFreeStirlingOrDigammaGuessAdmissible ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGammaLineageHighestAlphaBoundary : GammaLineageHighestAlphaBoundary
canonicalGammaLineageHighestAlphaBoundary =
  gamma-lineage-highest-alpha-boundary
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "The exact vendored PoleQuotientGammaBudget source identifies the epsGamma/gammaConeEnvelope producer and localizes the coarse high-ordinate scaling at stripConst's second-derivative L1 term. Historical producer discovery is therefore paid. The live historical route is repair/bypass of that localized C2 taper-norm estimate; the fresh same-g_pole theorem route remains independently admissible. RH remains open."

------------------------------------------------------------------------
-- FINAL-PAYMENT / HISTORICAL-REPAIR ROUTE SEPARATION
--
-- The terminal consumer is theorem-interface driven:
--
--   PoleQuotientGammaAllowancePayment
--
-- It does not consume a historical producer identifier. Therefore two proof
-- strategies remain legitimate and type-distinct:
--
--   freshFinalSameTaperTheorem
--     prove the final assigned allowance directly on the literal g_pole;
--
--   repairHistorical8889Producer
--     reuse the now-identified exact 8889 producer and repair/bypass its
--     localized stripConst precision loss until it instantiates the same final
--     allowance interface.
--
-- Provenance is mandatory for claims ABOUT the historical producer, not for an
-- independent theorem whose carrier/consumer identity is proved directly.
------------------------------------------------------------------------

data FinalGammaProofRoute : Set where
  freshFinalSameTaperTheorem : FinalGammaProofRoute
  repairHistorical8889Producer : FinalGammaProofRoute
  sourceFreeHistoricalLossGuess : FinalGammaProofRoute
  unrelatedGammaBound : FinalGammaProofRoute


data FinalGammaRouteState : Set where
  finalLive : FinalGammaRouteState
  historicalLive : FinalGammaRouteState
  prunedRoute : FinalGammaRouteState

finalGammaRouteState : FinalGammaProofRoute → FinalGammaRouteState
finalGammaRouteState freshFinalSameTaperTheorem = finalLive
finalGammaRouteState repairHistorical8889Producer = historicalLive
finalGammaRouteState sourceFreeHistoricalLossGuess = prunedRoute
finalGammaRouteState unrelatedGammaBound = prunedRoute

freshFinalGammaTheoremIsLive :
  finalGammaRouteState freshFinalSameTaperTheorem ≡ finalLive
freshFinalGammaTheoremIsLive = refl

historicalRepairRouteIsLive :
  finalGammaRouteState repairHistorical8889Producer ≡ historicalLive
historicalRepairRouteIsLive = refl

sourceFreeHistoricalGuessPruned :
  finalGammaRouteState sourceFreeHistoricalLossGuess ≡ prunedRoute
sourceFreeHistoricalGuessPruned = refl

unrelatedGammaBoundPruned :
  finalGammaRouteState unrelatedGammaBound ≡ prunedRoute
unrelatedGammaBoundPruned = refl

record FinalGammaRouteReconciliationBoundary : Set where
  constructor final-gamma-route-reconciliation-boundary
  field
    finalConsumerRequiresHistorical8889ProducerIdentity : Bool
    finalConsumerRequiresHistorical8889ProducerIdentityIsFalse :
      finalConsumerRequiresHistorical8889ProducerIdentity ≡ false

    historicalRepairRequiresHistoricalProducerIdentity : Bool
    historicalRepairRequiresHistoricalProducerIdentityIsTrue :
      historicalRepairRequiresHistoricalProducerIdentity ≡ true

    freshSameTaperFinalTheoremIsAdmissible : Bool
    freshSameTaperFinalTheoremIsAdmissibleIsTrue :
      freshSameTaperFinalTheoremIsAdmissible ≡ true

    historicalIdentityMayBeSkippedWhenAttributingLossTo8889 : Bool
    historicalIdentityMayBeSkippedWhenAttributingLossTo8889IsFalse :
      historicalIdentityMayBeSkippedWhenAttributingLossTo8889 ≡ false

    unrelatedGammaBoundPaysFinalConsumerWithoutCarrierIdentity : Bool
    unrelatedGammaBoundPaysFinalConsumerWithoutCarrierIdentityIsFalse :
      unrelatedGammaBoundPaysFinalConsumerWithoutCarrierIdentity ≡ false

    finalGammaAllowancePaymentClosedHere : Bool
    finalGammaAllowancePaymentClosedHereIsFalse :
      finalGammaAllowancePaymentClosedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    boundedReading : String

open FinalGammaRouteReconciliationBoundary public

canonicalFinalGammaRouteReconciliationBoundary :
  FinalGammaRouteReconciliationBoundary
canonicalFinalGammaRouteReconciliationBoundary =
  final-gamma-route-reconciliation-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "The final Gamma consumer asks for a theorem on the literal universal pole taper with the assigned allowance; it does not ask for historical provenance. Both a fresh same-g_pole theorem and a source-exact repair of 8889 remain live. On the historical route the producer identity and first precision-loss localization are now source-recovered, so the remaining work is the sharp stripConst/C2 repair plus theorem replay/transport. Neither route is completed here and RH remains open."
