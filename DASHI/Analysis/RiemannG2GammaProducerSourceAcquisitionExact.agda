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
-- Dependency-lower source layer. The companion dashi_lean4 repository now
-- vendors the exact 8889 PoleQuotientGammaBudget source. That theorem calls
-- gammaConeEnvelope directly, so generic family discovery and same-consumer
-- identity are no longer live.
--
-- The source itself locates the sharpness failure at the strip-constant C2
-- envelope: stripConst carries the sample-test second-derivative L1 norm, which
-- grows quadratically as the high-ordinate taper support shrinks. The live task
-- is to repair or bypass that exact estimate on the same literal taper.
------------------------------------------------------------------------

data GammaProducerRecoveryStage : Set where
  coarseBoundKnown : GammaProducerRecoveryStage
  candidateProducerRecovered : GammaProducerRecoveryStage
  finalProducerIdentityRequired : GammaProducerRecoveryStage
  producerDecompositionRecovered : GammaProducerRecoveryStage
  precisionLossLocalized : GammaProducerRecoveryStage
  sharpSameTaperRepairOwned : GammaProducerRecoveryStage

currentGammaProducerRecoveryStage : GammaProducerRecoveryStage
currentGammaProducerRecoveryStage = precisionLossLocalized

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
  findAnotherGenericGammaBound : GammaSourceSearchAction
  searchForAnyConcreteGammaFamily : GammaSourceSearchAction
  guessStirlingLossWithoutProducer : GammaSourceSearchAction
  guessDigammaLossWithoutProducer : GammaSourceSearchAction
  proveRecoveredCandidateIsFinal8889Producer : GammaSourceSearchAction
  recoverAlternateFinal8889Producer : GammaSourceSearchAction
  localizeFirstLossOnRecoveredProducer : GammaSourceSearchAction
  repairLocalizedSameTaperStep : GammaSourceSearchAction

SearchRelevant : GammaSourceSearchAction -> Set
SearchRelevant findAnotherGenericGammaBound = ⊥
SearchRelevant searchForAnyConcreteGammaFamily = ⊥
SearchRelevant guessStirlingLossWithoutProducer = ⊥
SearchRelevant guessDigammaLossWithoutProducer = ⊥
SearchRelevant proveRecoveredCandidateIsFinal8889Producer = ⊥
SearchRelevant recoverAlternateFinal8889Producer = ⊥
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

------------------------------------------------------------------------
-- Bounded source-history status. These booleans record the exact vendored-source
-- audit; they still do not transport a Lean proof term into Agda.
------------------------------------------------------------------------

record GammaProducerSourceAcquisitionBoundary : Set where
  constructor gamma-producer-source-acquisition-boundary
  field
    concreteCandidateGammaProducerFamilyRecovered : Bool
    concreteCandidateGammaProducerFamilyRecoveredIsTrue :
      concreteCandidateGammaProducerFamilyRecovered ≡ true

    exactUniformGammaProducerIdentityRecoveredOnThisBranch : Bool
    exactUniformGammaProducerIdentityRecoveredOnThisBranchIsTrue :
      exactUniformGammaProducerIdentityRecoveredOnThisBranch ≡ true

    firstPrecisionLosingAnalyticStepRecovered : Bool
    firstPrecisionLosingAnalyticStepRecoveredIsTrue :
      firstPrecisionLosingAnalyticStepRecovered ≡ true

    genericGammaSourceSearchStillLive : Bool
    genericGammaSourceSearchStillLiveIsFalse :
      genericGammaSourceSearchStillLive ≡ false

    genericAsymptoticGuessCanReplaceProducerIdentity : Bool
    genericAsymptoticGuessCanReplaceProducerIdentityIsFalse :
      genericAsymptoticGuessCanReplaceProducerIdentity ≡ false

    sameConsumerProducerIdentityIsStillLive : Bool
    sameConsumerProducerIdentityIsStillLiveIsFalse :
      sameConsumerProducerIdentityIsStillLive ≡ false

    sharpGammaRepairStillOpen : Bool
    sharpGammaRepairStillOpenIsTrue : sharpGammaRepairStillOpen ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    candidateSourceReference : String
    highestAlphaReading : String

canonicalGammaProducerSourceAcquisitionBoundary :
  GammaProducerSourceAcquisitionBoundary
canonicalGammaProducerSourceAcquisitionBoundary =
  gamma-producer-source-acquisition-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "vendored Imported/Zeta23Bridge/Zeta23Bridge/PoleQuotientGammaBudget.lean -> LiteralWeilGammaConeBound.gammaConeEnvelope"
    "A concrete epsGamma/gammaConeEnvelope Gamma producer family and downstream residual use are already recovered, so generic source discovery is pruned. The live source payment is same-consumer identity: prove that this recovered chain produces the exact 8889 universal pole-quotient Gamma bound, or recover the actual alternate 8889 producer. Do not localize Stirling, digamma, envelope, norm, uniformisation or remainder loss before that identity. After identity, localize the first precision-losing transformation and repair only that step until the final assigned allowance B_Gamma <= A_Gamma is met."
