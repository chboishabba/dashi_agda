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
-- Dependency-lower source layer. Retained source history now gives one concrete
-- candidate family, epsGamma / gammaConeEnvelope, so generic family discovery is
-- no longer the search target. This module deliberately does NOT import the
-- higher `GammaCandidateSourceLineageRecoveryExact` owner (which itself imports
-- this file); doing so would create an import cycle.
--
-- The remaining source payment is same-consumer identity: prove that the
-- recovered candidate family is the exact 8889 pole-quotient uniform-bound
-- producer, or recover the actual alternate producer. Only after that identity
-- may the first precision-losing transformation be localized without guessing.
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
-- Bounded source-history status. These booleans record the later retained-source
-- audit; they do not transport a Lean proof term or identify the candidate with
-- the 8889 consumer. The higher lineage owner carries the detailed provenance.
------------------------------------------------------------------------

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

    candidateSourceReference : String
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
    "retained Zeta23Bridge/LiteralWeilGammaConeBound.lean: epsGamma / gammaConeEnvelope; detailed provenance is owned by RiemannG2GammaCandidateSourceLineageRecoveryExact"
    "A concrete epsGamma/gammaConeEnvelope Gamma producer family and downstream residual use are already recovered, so generic source discovery is pruned. The live source payment is same-consumer identity: prove that this recovered chain produces the exact 8889 universal pole-quotient Gamma bound, or recover the actual alternate 8889 producer. Do not localize Stirling, digamma, envelope, norm, uniformisation or remainder loss before that identity. After identity, localize the first precision-losing transformation and repair only that step until the final assigned allowance B_Gamma <= A_Gamma is met."
