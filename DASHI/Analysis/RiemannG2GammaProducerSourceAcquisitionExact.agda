module DASHI.Analysis.RiemannG2GammaProducerSourceAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ8889
import DASHI.Analysis.RiemannG2GammaPrecisionLossLocalizationExact as Localization

------------------------------------------------------------------------
-- GAMMA PRODUCER SOURCE ACQUISITION
--
-- Repo-first BIDI result after the 8889 return:
--
--   * existence of a uniform Gamma upper bound is already checked in Lean;
--   * that bound misses the sharp pole-quotient accuracy window;
--   * the current recovered Agda/PR surface does not identify the internal
--     producer decomposition or the first estimate responsible for the loss.
--
-- Therefore it is unsound to jump directly to a guessed Stirling/digamma/
-- envelope repair.  The next payment is source-exact recovery of the actual
-- same-taper Gamma producer chain, followed by a proof-relevant localization of
-- the first precision-losing step.
------------------------------------------------------------------------

data GammaProducerRecoveryStage : Set where
  coarseBoundKnown
  producerArtifactRequired
  producerDecompositionRecovered
  precisionLossLocalized
  sharpSameTaperRepairOwned
  : GammaProducerRecoveryStage

currentGammaProducerRecoveryStage : GammaProducerRecoveryStage
currentGammaProducerRecoveryStage = producerArtifactRequired

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
  guessStirlingLossWithoutProducer
  guessDigammaLossWithoutProducer
  recoverExactUniformBoundArtifact
  recoverExactProducerDecomposition
  localizeFirstLossOnRecoveredProducer
  repairLocalizedSameTaperStep
  : GammaSourceSearchAction

SearchRelevant : GammaSourceSearchAction -> Set
SearchRelevant findAnotherGenericGammaBound = ⊥
SearchRelevant guessStirlingLossWithoutProducer = ⊥
SearchRelevant guessDigammaLossWithoutProducer = ⊥
SearchRelevant recoverExactUniformBoundArtifact = ⊤
SearchRelevant recoverExactProducerDecomposition = ⊤
SearchRelevant localizeFirstLossOnRecoveredProducer = ⊤
SearchRelevant repairLocalizedSameTaperStep = ⊤

findAnotherGenericGammaBoundPruned :
  SearchRelevant findAnotherGenericGammaBound -> ⊥
findAnotherGenericGammaBoundPruned x = x

guessStirlingLossWithoutProducerPruned :
  SearchRelevant guessStirlingLossWithoutProducer -> ⊥
guessStirlingLossWithoutProducerPruned x = x

guessDigammaLossWithoutProducerPruned :
  SearchRelevant guessDigammaLossWithoutProducer -> ⊥
guessDigammaLossWithoutProducerPruned x = x

------------------------------------------------------------------------
-- Exact inherited facts from the 8889 reconciliation.
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

record GammaProducerSourceAcquisitionBoundary : Set where
  constructor gamma-producer-source-acquisition-boundary
  field
    exactUniformGammaProducerArtifactRecoveredOnThisBranch : Bool
    exactUniformGammaProducerArtifactRecoveredOnThisBranchIsFalse :
      exactUniformGammaProducerArtifactRecoveredOnThisBranch ≡ false

    firstPrecisionLosingAnalyticStepRecovered : Bool
    firstPrecisionLosingAnalyticStepRecoveredIsFalse :
      firstPrecisionLosingAnalyticStepRecovered ≡ false

    genericAsymptoticGuessCanReplaceProducerRecovery : Bool
    genericAsymptoticGuessCanReplaceProducerRecoveryIsFalse :
      genericAsymptoticGuessCanReplaceProducerRecovery ≡ false

    sourceExactProducerRecoveryIsLive : Bool
    sourceExactProducerRecoveryIsLiveIsTrue :
      sourceExactProducerRecoveryIsLive ≡ true

    sharpGammaRepairStillOpen : Bool
    sharpGammaRepairStillOpenIsTrue : sharpGammaRepairStillOpen ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGammaProducerSourceAcquisitionBoundary :
  GammaProducerSourceAcquisitionBoundary
canonicalGammaProducerSourceAcquisitionBoundary =
  gamma-producer-source-acquisition-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    "The 8889 return proves that a uniform Gamma bound exists and is too coarse, but the currently recovered theorem surface does not identify which internal estimate loses the sharp O(|t|^-2) window. Do not guess Stirling, digamma, envelope, or remainder as the culprit. Recover the exact same-taper uniform-bound producer and its decomposition first; then instantiate GammaPrecisionLossLocalization at the first source-verified losing step and repair only that step."
