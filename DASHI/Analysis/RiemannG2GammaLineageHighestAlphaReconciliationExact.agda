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
-- The generic acquisition owner predates recovery of retained source history.
-- We now know one concrete source family:
--
--   LiteralWeilGammaConeBound.epsGamma
--   LiteralWeilGammaConeBound.gammaConeEnvelope
--     -> LiteralWeilTwoRadiusResidualEnvelope.abs_residualCone_le.
--
-- What remains unknown on THAT HISTORICAL REPAIR ROUTE is whether the reported
-- 8889 pole-quotient uniform Gamma producer is this exact source chain (or
-- another one). Precision-loss localization of the historical producer is
-- blocked until that same-consumer provenance edge is proved.
--
-- This is not a global prerequisite for the terminal RH consumer. A fresh,
-- theorem-bearing same-g_pole proof of the final Gamma allowance payment may be
-- constructed independently of the 8889 implementation. Historical identity is
-- required only before attributing/localising/repairing loss inside 8889.
------------------------------------------------------------------------

data GammaHighestAlphaPayment : Set where
  discoverAnyConcreteGammaSourceFamily
  recoverEpsGammaEnvelopeLineage
  proveLineageIs8889PoleQuotientProducer
  recoverAlternate8889ProducerIfNot
  localizeFirstLossBeforeConsumerIdentity
  localizeFirstLossAfterConsumerIdentity
  repairIdentifiedLoss
  : GammaHighestAlphaPayment

data PaymentState : Set where
  pruned owned live blocked downstream : PaymentState

paymentState : GammaHighestAlphaPayment → PaymentState
paymentState discoverAnyConcreteGammaSourceFamily = pruned
paymentState recoverEpsGammaEnvelopeLineage = owned
paymentState proveLineageIs8889PoleQuotientProducer = live
paymentState recoverAlternate8889ProducerIfNot = live
paymentState localizeFirstLossBeforeConsumerIdentity = blocked
paymentState localizeFirstLossAfterConsumerIdentity = downstream
paymentState repairIdentifiedLoss = downstream

concreteSourceDiscoveryPruned :
  paymentState discoverAnyConcreteGammaSourceFamily ≡ pruned
concreteSourceDiscoveryPruned = refl

candidateLineageOwned :
  paymentState recoverEpsGammaEnvelopeLineage ≡ owned
candidateLineageOwned = refl

sameConsumerIdentityLive :
  paymentState proveLineageIs8889PoleQuotientProducer ≡ live
sameConsumerIdentityLive = refl

localizationBeforeIdentityBlocked :
  paymentState localizeFirstLossBeforeConsumerIdentity ≡ blocked
localizationBeforeIdentityBlocked = refl

candidateOwnerAgreesSourceFamilyRecovered :
  Candidate.concreteGammaSourceFamilyRecovered
    Candidate.canonicalGammaCandidateLineageBoundary ≡ true
candidateOwnerAgreesSourceFamilyRecovered =
  Candidate.concreteGammaSourceFamilyRecoveredIsTrue
    Candidate.canonicalGammaCandidateLineageBoundary

candidateOwnerAgreesConsumerIdentityOpen :
  Candidate.exact8889ConsumerIdentityRecovered
    Candidate.canonicalGammaCandidateLineageBoundary ≡ false
candidateOwnerAgreesConsumerIdentityOpen =
  Candidate.exact8889ConsumerIdentityRecoveredIsFalse
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
    sameConsumer8889ProvenanceStillRequiredIsTrue :
      sameConsumer8889ProvenanceStillRequired ≡ true

    sourcePrecisionLossLocalizationAdmissibleBeforeThatIdentity : Bool
    sourcePrecisionLossLocalizationAdmissibleBeforeThatIdentityIsFalse :
      sourcePrecisionLossLocalizationAdmissibleBeforeThatIdentity ≡ false

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
    true refl
    false refl
    false refl
    false refl
    "On the historical 8889-repair route, retained Zeta23 source history recovers a theorem-bearing epsGamma/gammaConeEnvelope lineage but not its identity with the 8889 pole-quotient producer. Recover that provenance edge, or the actual alternate producer, before localising loss inside 8889. This statement is route-local: it does not block an independently proved final same-g_pole Gamma allowance theorem. Source-free guesses may not be represented as historical precision-loss localisation. RH remains open."

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
--     first identify the exact 8889 producer, then localise and repair its
--     precision loss until it instantiates the same final allowance interface.
--
-- Provenance is mandatory for claims ABOUT the historical producer, not for an
-- independent theorem whose carrier/consumer identity is proved directly.
------------------------------------------------------------------------

data FinalGammaProofRoute : Set where
  freshFinalSameTaperTheorem
  repairHistorical8889Producer
  sourceFreeHistoricalLossGuess
  unrelatedGammaBound
  : FinalGammaProofRoute

data FinalGammaRouteState : Set where
  finalLive historicalLive prunedRoute : FinalGammaRouteState

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
    "The final Gamma consumer asks for a theorem on the literal universal pole taper with the assigned allowance; it does not ask for the identity of the historical 8889 implementation. Therefore a fresh same-g_pole theorem and a source-exact repair of 8889 are both live proof routes. The latter requires producer identity before any precision-loss attribution; the former requires direct carrier/taper/consumer identity instead. Neither route is completed here and RH remains open."
