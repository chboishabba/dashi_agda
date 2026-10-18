module DASHI.Analysis.RiemannG2GammaCandidateSourceLineageRecoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GammaProducerSourceAcquisitionExact as Acquisition
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as Return8889

------------------------------------------------------------------------
-- RECOVERED EXACT 8889 GAMMA SOURCE LINEAGE
--
-- The companion dashi_lean4 repository vendors both the original envelope
--
--   LiteralWeilGammaConeBound.gammaConeEnvelope
--
-- and the exact pole-quotient consumer
--
--   PoleQuotientGammaBudget.exists_gamma_budget_linear_in_stripConst.
--
-- The latter calls gammaConeEnvelope directly.  Therefore the historical
-- epsGamma/gammaConeEnvelope chain is now source-identified with the reported
-- 8889 pole-quotient Gamma producer.  This is source custody, not Agda proof
-- transport.
--
-- The producer's own source commentary also identifies why it misses the sharp
-- window: stripConst carries a second-derivative L1 term which grows
-- quadratically when the high-ordinate taper support shrinks.
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
    sameAsReported8889PoleQuotientGammaProducerIsTrue :
      sameAsReported8889PoleQuotientGammaProducer ≡ true

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
    true refl
    "Vendored dashi_lean4 now contains the exact 8889 PoleQuotientGammaBudget.lean source. Its theorem exists_gamma_budget_linear_in_stripConst invokes gammaConeEnvelope directly, so the epsGamma/gammaConeEnvelope chain is no longer merely a candidate: the same-consumer producer lineage is source-recovered. The remaining work is quantitative repair/bypass of the strip-constant envelope, not producer identity."

------------------------------------------------------------------------
-- Exact search consequence.
------------------------------------------------------------------------

data GammaLineagePayment : Set where
  searchForAnyConcreteGammaSourceFamily : GammaLineagePayment
  recoverCandidateGammaEnvelopeFamily : GammaLineagePayment
  proveCandidateFeeds8889PoleQuotientBound : GammaLineagePayment
  localizePrecisionLossInsideCandidateBeforeIdentity : GammaLineagePayment
  localizePrecisionLossAfterSameConsumerIdentity : GammaLineagePayment


data PaymentStatus : Set where
  pruned : PaymentStatus
  owned : PaymentStatus
  live : PaymentStatus
  blocked : PaymentStatus
  downstream : PaymentStatus

paymentStatus : GammaLineagePayment → PaymentStatus
paymentStatus searchForAnyConcreteGammaSourceFamily = pruned
paymentStatus recoverCandidateGammaEnvelopeFamily = owned
paymentStatus proveCandidateFeeds8889PoleQuotientBound = owned
paymentStatus localizePrecisionLossInsideCandidateBeforeIdentity = pruned
paymentStatus localizePrecisionLossAfterSameConsumerIdentity = live

concreteGammaSourceSearchPruned :
  paymentStatus searchForAnyConcreteGammaSourceFamily ≡ pruned
concreteGammaSourceSearchPruned = refl

candidateGammaFamilyOwned :
  paymentStatus recoverCandidateGammaEnvelopeFamily ≡ owned
candidateGammaFamilyOwned = refl

candidateTo8889SameConsumerIdentityRecovered :
  paymentStatus proveCandidateFeeds8889PoleQuotientBound ≡ owned
candidateTo8889SameConsumerIdentityRecovered = refl

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
    exact8889ConsumerIdentityRecoveredIsTrue :
      exact8889ConsumerIdentityRecovered ≡ true

    precisionLossLocalizationNowUnblocked : Bool
    precisionLossLocalizationNowUnblockedIsTrue :
      precisionLossLocalizationNowUnblocked ≡ true

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
    true refl
    true refl
    false refl
    false refl
    "The exact vendored 8889 file PoleQuotientGammaBudget.lean is now present in dashi_lean4 and its final budget theorem uses gammaConeEnvelope directly. Same-consumer Gamma lineage is therefore recovered. The file itself explains the sharpness failure: stripConst contains a second-derivative L1 term which grows quadratically as the high-ordinate taper support shrinks. The live Gamma work is now quantitative repair of that strip/C2 envelope or a fresh sharper same-taper theorem. RH remains open."
