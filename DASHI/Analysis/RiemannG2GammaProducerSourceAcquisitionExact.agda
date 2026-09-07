module DASHI.Analysis.RiemannG2GammaProducerSourceAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ8889
import DASHI.Analysis.RiemannG2GammaPrecisionLossLocalizationExact as Localization
import DASHI.Analysis.RiemannG2GammaCandidateSourceLineageRecoveryExact as Candidate

------------------------------------------------------------------------
-- GAMMA PRODUCER SOURCE ACQUISITION
--
-- Repo-first corrected state after the retained source-history recovery:
--
--   * existence of a uniform Gamma upper bound is already checked in Lean;
--   * that bound misses the sharp pole-quotient accuracy window;
--   * a concrete epsGamma / gammaConeEnvelope source family and downstream use
--     have now been recovered;
--   * what is NOT recovered is the theorem that identifies that candidate family
--     with the exact 8889 pole-quotient uniform-bound producer.
--
-- Therefore generic producer-source discovery is no longer the live task. The
-- source payment is same-consumer identity: either prove that the recovered
-- epsGamma/gammaConeEnvelope chain is the 8889 producer, or recover the actual
-- alternate producer chain. Only after that identity is owned may the first
-- precision-losing transformation be localized without guessing.
------------------------------------------------------------------------

data GammaProducerRecoveryStage : Set where
  coarseBoundKnown
  candidateProducerRecovered
  finalProducerIdentityRequired
  producerDecompositionRecovered
  precisionLossLocalized
  sharpSameTaperRepairOwned
  : GammaProducerRecoveryStage

currentGammaProducerRecoveryStage : GammaProducerRecoveryStage
currentGammaProducerRecoveryStage = finalProducerIdentityRequired

record GammaProducerSourceArtifact : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget
    sameLiteralPoleQuotientTaper : Set
    theoremOrArtifactReference : String
    exactProducerDecomposition : Set
    decompositionFeedsReportedUniformBound : Set

open GammaProducerSourceArtifact public

record GammaProducerSourceLocalization
    (artifact : GammaProducerSourceArtifact) : Set₁ where
  field
    coarseProducer : Localization.ExistingCoarseGammaProducer
    sameTarget : Localization.target coarseProducer ≡ target artifact
    localization : Localization.GammaPrecisionLossLocalization coarseProducer
    localizationUsesRecoveredDecomposition : Set

open GammaProducerSourceLocalization public

------------------------------------------------------------------------
-- Search actions.
------------------------------------------------------------------------

data GammaSourceSearchAction : Set where
  findAnotherGenericGammaBound
  searchForAnyConcreteGammaFamily
  guessStirlingLossWithoutProducer
  guessDigammaLossWithoutProducer
  proveRecoveredCandidateIsFinal8889Producer
  recoverAlternateFinal8889Producer
  localizeFirstLossOnRecoveredProducer
  repairLocalizedSameTaperStep
  : GammaSourceSearchAction

SearchRelevant : GammaSourceSearchAction -> Set
SearchRelevant findAnotherGenericGammaBound = ⊥
SearchRelevant searchForAnyConcreteGammaFamily = ⊥
SearchRelevant guessStirlingLossWithoutProducer = ⊥
SearchRelevant guessDigammaLossWithoutProducer = ⊥
SearchRelevant proveRecoveredCandidateIsFinal8889Producer = ⊤
SearchRelevant recoverAlternateFinal8889Producer = ⊤
SearchRelevant localizeFirstLossOnRecoveredProducer = ⊤
SearchRelevant repairLocalizedSameTaperStep = ⊤

findAnotherGenericGammaBoundPruned :
  SearchRelevant findAnotherGenericGammaBound -> ⊥
findAnotherGenericGammaBoundPruned x = x

searchForAnyConcreteGammaFamilyPruned :
  SearchRelevant searchForAnyConcreteGammaFamily -> ⊥
searchForAnyConcreteGammaFamilyPruned x = x

guessStirlingLossWithoutProducerPruned :
  SearchRelevant guessStirlingLossWithoutProducer -> ⊥
guessStirlingLossWithoutProducerPruned x = x

guessDigammaLossWithoutProducerPruned :
  SearchRelevant guessDigammaLossWithoutProducer -> ⊥
guessDigammaLossWithoutProducerPruned x = x

------------------------------------------------------------------------
-- Exact inherited facts from the 8889 reconciliation and later source recovery.
------------------------------------------------------------------------

uniformGammaBoundExistenceAlreadyOwned :
  PQ8889.gammaUniformBoundOwned
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ true
uniformGammaBoundExistenceAlreadyOwned =
  PQ8889.gammaUniformBoundOwnedIsTrue
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889

uniformGammaBoundAlreadyKnownTooCoarse :
  PQ8889.gammaUniformBoundFitsRequiredWindow
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ false
uniformGammaBoundAlreadyKnownTooCoarse =
  PQ8889.gammaUniformBoundFitsRequiredWindowIsFalse
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889

checkedLeanProofStillNotTransported :
  PQ8889.transportedIntoAgda
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ false
checkedLeanProofStillNotTransported =
  PQ8889.transportedIntoAgdaIsFalse
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889

concreteCandidateGammaFamilyRecovered :
  Candidate.GammaCandidateLineageBoundary.concreteGammaSourceFamilyRecovered
    Candidate.canonicalGammaCandidateLineageBoundary ≡ true
concreteCandidateGammaFamilyRecovered = refl

candidateIdentityWithFinal8889ProducerStillOpen :
  Candidate.GammaCandidateLineageBoundary.exact8889ConsumerIdentityRecovered
    Candidate.canonicalGammaCandidateLineageBoundary ≡ false
candidateIdentityWithFinal8889ProducerStillOpen = refl

record GammaProducerSourceAcquisitionBoundary : Set where
  constructor gamma-producer-source-acquisition-boundary
  field
    concreteCandidateGammaProducerFamilyRecovered : Bool
    concreteCandidateGammaProducerFamilyRecoveredIsTrue :
      concreteCandidateGammaProducerFamilyRecovered ≡ true

    exactUniformGammaProducerIdentityRecoveredOnThisBranch : Bool
    exactUniformGammaProducerIdentityRecoveredOnThisBranchIsFalse :
      exactUniformGammaProducerIdentityRecoveredOnThisBranch ≡ false

    firstPrecisionLosingAnalyticStepRecovered : Bool
    firstPrecisionLosingAnalyticStepRecoveredIsFalse :
      firstPrecisionLosingAnalyticStepRecovered ≡ false

    genericGammaSourceSearchStillLive : Bool
    genericGammaSourceSearchStillLiveIsFalse :
      genericGammaSourceSearchStillLive ≡ false

    genericAsymptoticGuessCanReplaceProducerIdentity : Bool
    genericAsymptoticGuessCanReplaceProducerIdentityIsFalse :
      genericAsymptoticGuessCanReplaceProducerIdentity ≡ false

    sameConsumerProducerIdentityIsLive : Bool
    sameConsumerProducerIdentityIsLiveIsTrue :
      sameConsumerProducerIdentityIsLive ≡ true

    sharpGammaRepairStillOpen : Bool
    sharpGammaRepairStillOpenIsTrue : sharpGammaRepairStillOpen ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGammaProducerSourceAcquisitionBoundary :
  GammaProducerSourceAcquisitionBoundary
canonicalGammaProducerSourceAcquisitionBoundary =
  gamma-producer-source-acquisition-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    "A concrete epsGamma/gammaConeEnvelope Gamma producer family and downstream residual use are already recovered, so generic source discovery is pruned. The live source payment is same-consumer identity: prove that this recovered chain produces the exact 8889 universal pole-quotient Gamma bound, or recover the actual alternate 8889 producer. Do not localize Stirling, digamma, envelope, norm, uniformisation or remainder loss before that identity. After identity, localize the first precision-losing transformation and repair only that step until the final assigned allowance B_Gamma <= A_Gamma is met."
