module DASHI.Analysis.RiemannG2GammaCandidateSourceLineageRecoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GammaProducerSourceAcquisitionExact as Acquisition
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as Return8889

------------------------------------------------------------------------
-- RECOVERED GAMMA SOURCE FAMILY, WITHOUT SAME-CONSUMER PROMOTION
--
-- Retained checked-source artifacts expose an actual Gamma estimate family:
--
--   Zeta23Bridge/LiteralWeilGammaConeBound.lean
--     epsGamma
--     gammaConeEnvelope
--
-- and a downstream theorem-bearing consumer:
--
--   LiteralWeilTwoRadiusResidualEnvelope.abs_residualCone_le
--
-- whose residual envelope is
--
--   epsZero + epsGamma + 4 * |poleEvenResp|.
--
-- This materially improves source acquisition: a concrete Gamma producer family
-- and downstream use are known.  But the retained artifact inspected here is an
-- earlier two-radius/projective lane.  We have not recovered an exact theorem
-- stating that the 8889 pole-quotient uniform Gamma bound is produced by this
-- same gammaConeEnvelope/epsGamma chain.  Therefore this module refuses to set
-- Acquisition.GammaProducerSourceArtifact.decompositionFeedsReportedUniformBound.
------------------------------------------------------------------------

record RecoveredGammaCandidateLineage : Set where
  constructor recovered-gamma-candidate-lineage
  field
    sourceModule : String
    epsilonDefinition : String
    envelopeTheorem : String
    downstreamModule : String
    downstreamTheorem : String

    literalGammaChannelRecovered : Bool
    literalGammaChannelRecoveredIsTrue : literalGammaChannelRecovered ≡ true

    explicitGammaEnvelopeRecovered : Bool
    explicitGammaEnvelopeRecoveredIsTrue : explicitGammaEnvelopeRecovered ≡ true

    downstreamResidualUsesSameEnvelopeSymbol : Bool
    downstreamResidualUsesSameEnvelopeSymbolIsTrue :
      downstreamResidualUsesSameEnvelopeSymbol ≡ true

    sameAsReported8889PoleQuotientGammaProducer : Bool
    sameAsReported8889PoleQuotientGammaProducerIsFalse :
      sameAsReported8889PoleQuotientGammaProducer ≡ false

    lineageReference : String

open RecoveredGammaCandidateLineage public

canonicalRecoveredGammaCandidateLineage : RecoveredGammaCandidateLineage
canonicalRecoveredGammaCandidateLineage =
  recovered-gamma-candidate-lineage
    "Zeta23Bridge/LiteralWeilGammaConeBound.lean"
    "Zeta23Bridge.LiteralWeilGammaConeBound.epsGamma"
    "Zeta23Bridge.LiteralWeilGammaConeBound.gammaConeEnvelope"
    "Zeta23Bridge/LiteralWeilTwoRadiusResidualEnvelope.lean"
    "Zeta23Bridge.LiteralWeilTwoRadiusResidualEnvelope.abs_residualCone_le"
    true refl
    true refl
    true refl
    false refl
    "Retained Zeta23Bridge source history recovers the concrete epsGamma/gammaConeEnvelope family and its use inside epsResidual. This is a real candidate Gamma producer lineage. It is not promoted to the 8889 pole-quotient Gamma producer until an exact source/provenance theorem identifies that consumer with this chain."

------------------------------------------------------------------------
-- Exact search consequence.
------------------------------------------------------------------------

data GammaLineagePayment : Set where
  searchForAnyConcreteGammaSourceFamily
  recoverCandidateGammaEnvelopeFamily
  proveCandidateFeeds8889PoleQuotientBound
  localizePrecisionLossInsideCandidateBeforeIdentity
  localizePrecisionLossAfterSameConsumerIdentity
  : GammaLineagePayment

data PaymentStatus : Set where
  pruned owned live blocked downstream : PaymentStatus

paymentStatus : GammaLineagePayment → PaymentStatus
paymentStatus searchForAnyConcreteGammaSourceFamily = pruned
paymentStatus recoverCandidateGammaEnvelopeFamily = owned
paymentStatus proveCandidateFeeds8889PoleQuotientBound = live
paymentStatus localizePrecisionLossInsideCandidateBeforeIdentity = blocked
paymentStatus localizePrecisionLossAfterSameConsumerIdentity = downstream

concreteGammaSourceSearchPruned :
  paymentStatus searchForAnyConcreteGammaSourceFamily ≡ pruned
concreteGammaSourceSearchPruned = refl

candidateGammaFamilyOwned :
  paymentStatus recoverCandidateGammaEnvelopeFamily ≡ owned
candidateGammaFamilyOwned = refl

candidateTo8889SameConsumerIdentityStillLive :
  paymentStatus proveCandidateFeeds8889PoleQuotientBound ≡ live
candidateTo8889SameConsumerIdentityStillLive = refl

------------------------------------------------------------------------
-- Cross-check against the checked-return boundary.
------------------------------------------------------------------------

reported8889GammaBoundExists :
  Return8889.gammaUniformBoundOwned
    Return8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ true
reported8889GammaBoundExists =
  Return8889.gammaUniformBoundOwnedIsTrue
    Return8889.canonicalCheckedLeanPoleQuotientReturn8889

reported8889GammaBoundStillMissesWindow :
  Return8889.gammaUniformBoundFitsRequiredWindow
    Return8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ false
reported8889GammaBoundStillMissesWindow =
  Return8889.gammaUniformBoundFitsRequiredWindowIsFalse
    Return8889.canonicalCheckedLeanPoleQuotientReturn8889

record GammaCandidateLineageBoundary : Set where
  constructor gamma-candidate-lineage-boundary
  field
    concreteGammaSourceFamilyRecovered : Bool
    concreteGammaSourceFamilyRecoveredIsTrue :
      concreteGammaSourceFamilyRecovered ≡ true

    exact8889ConsumerIdentityRecovered : Bool
    exact8889ConsumerIdentityRecoveredIsFalse :
      exact8889ConsumerIdentityRecovered ≡ false

    precisionLossMayBeLocalizedBeforeConsumerIdentity : Bool
    precisionLossMayBeLocalizedBeforeConsumerIdentityIsFalse :
      precisionLossMayBeLocalizedBeforeConsumerIdentity ≡ false

    genericGammaSourceSearchStillHighestAlpha : Bool
    genericGammaSourceSearchStillHighestAlphaIsFalse :
      genericGammaSourceSearchStillHighestAlpha ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGammaCandidateLineageBoundary : GammaCandidateLineageBoundary
canonicalGammaCandidateLineageBoundary =
  gamma-candidate-lineage-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    "The retained checked Zeta23 source history recovers a concrete Gamma envelope family, epsGamma/gammaConeEnvelope, and a theorem-bearing downstream residual use. Generic source discovery is therefore pruned. However the current 8889 pole-quotient consumer is not yet proved to use this exact producer chain. The next source payment is same-consumer provenance: identify the reported uniform pole-quotient Gamma bound with this recovered chain or recover the actual alternate chain. Only after that identity may a first precision-losing transformation be localized and repaired. RH remains open."
