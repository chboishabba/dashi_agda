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
-- What remains unknown is not whether a concrete Gamma estimate exists.  It is
-- whether the reported 8889 pole-quotient uniform Gamma producer is THIS exact
-- source chain (or another one).  Precision-loss localization is blocked until
-- that same-consumer provenance edge is proved.
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
    "Retained Zeta23 source history recovers a concrete theorem-bearing Gamma envelope lineage, epsGamma/gammaConeEnvelope, and its downstream use in the two-radius residual envelope. Therefore generic Gamma artifact discovery is no longer highest alpha. But the current 8889 pole-quotient uniform Gamma producer has not yet been proved to be this exact chain. Recover that same-consumer provenance edge, or recover the alternate actual 8889 chain. Only then localize the first precision-losing transformation and repair it. Do not guess Stirling/digamma loss from source shape alone. RH remains open."
