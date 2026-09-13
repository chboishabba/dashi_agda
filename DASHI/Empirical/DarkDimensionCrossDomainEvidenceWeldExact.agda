module DASHI.Empirical.DarkDimensionCrossDomainEvidenceWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact as AcquisitionAssessment
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact as BedroyaBackground
import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as BedroyaManifest
import DASHI.Empirical.DarkDimensionDAOSameKeyReconstructionRunExact as DAORun

------------------------------------------------------------------------
-- CROSS-DOMAIN EVIDENCE WELD
------------------------------------------------------------------------

data CurrentSearchResult : Set where
  located : CurrentSearchResult
  searchedButNotLocated : CurrentSearchResult

bedroyaImplementationSearchResult : CurrentSearchResult
bedroyaImplementationSearchResult = searchedButNotLocated

data SearchNonlocationEqualsKnownAbsence : Set where

notLocatedDoesNotBecomeAbsent : SearchNonlocationEqualsKnownAbsence → ⊥
notLocatedDoesNotBecomeAbsent ()

acquisitionNoMatchDoesNotBecomeAbsence :
  AcquisitionAssessment.NoMatchIsNegativeWorldFact → ⊥
acquisitionNoMatchDoesNotBecomeAbsence =
  AcquisitionAssessment.noMatchDoesNotBecomeNegativeFact

bedroyaChainSearchDiligence : Diligence.SourceDiligence
bedroyaChainSearchDiligence =
  Diligence.source-diligence
    "first-party Bedroya / predecessor executable chain or configuration"
    BedroyaBackground.bedroyaBackgroundSource
    Diligence.implementationEvidence
    true
    refl
    "targeted paper / GitHub / repository / archive search; non-location retained as bounded result"
    Diligence.primaryUnavailable
    "no exact first-party chain/config locator admitted by this tranche"
    "search state current to the #907 acquisition pass"
    "same-object requires authors/model implementation or explicitly source-bound chain"
    "2021 predecessor through 2026 Bedroya analysis"
    "search covered named paper/authors/predecessor and public code/archive surfaces; not exhaustive of private or unindexed holdings"
    "paper equations and plots located; executable chain/config contradiction search remained open"
    "non-location is not nonexistence and cannot be promoted to an absence claim"
    "downstream numerical reproduction remains blocked until exact manifest/normalization custody is paid"

------------------------------------------------------------------------
-- Abstract finite non-factorability witness over the declared carriers only.
------------------------------------------------------------------------

data MarginalSummaryState : Set where
  sameMarginalsVectorA : MarginalSummaryState
  sameMarginalsVectorB : MarginalSummaryState

data PlottedMarginals : Set where
  samePublishedMarginals : PlottedMarginals

data SixKeyVectorIdentity : Set where
  sixKeyVectorA : SixKeyVectorIdentity
  sixKeyVectorB : SixKeyVectorIdentity

publishedMarginalProjection : MarginalSummaryState → PlottedMarginals
publishedMarginalProjection sameMarginalsVectorA = samePublishedMarginals
publishedMarginalProjection sameMarginalsVectorB = samePublishedMarginals

sixKeyVectorProjection : MarginalSummaryState → SixKeyVectorIdentity
sixKeyVectorProjection sameMarginalsVectorA = sixKeyVectorA
sixKeyVectorProjection sameMarginalsVectorB = sixKeyVectorB

sixKeyVectorsDiffer :
  sixKeyVectorProjection sameMarginalsVectorA ≡
  sixKeyVectorProjection sameMarginalsVectorB → ⊥
sixKeyVectorsDiffer ()

sameMarginalsDifferentSixKeyWitness :
  NonFactor.NonFactorabilityWitness
    publishedMarginalProjection
    sixKeyVectorProjection
sameMarginalsDifferentSixKeyWitness =
  NonFactor.nonFactorabilityWitness
    sameMarginalsVectorA
    sameMarginalsVectorB
    refl
    sixKeyVectorsDiffer

marginalsCannotFactorToUniqueSixKeyVector :
  NonFactor.FactorsThrough
    publishedMarginalProjection
    sixKeyVectorProjection →
  ⊥
marginalsCannotFactorToUniqueSixKeyVector =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    sameMarginalsDifferentSixKeyWitness

publishedMarginalsCannotAutoDetermineSixKeyVector :
  NonFactor.FactorsThrough
    publishedMarginalProjection
    sixKeyVectorProjection →
  ⊥
publishedMarginalsCannotAutoDetermineSixKeyVector =
  marginalsCannotFactorToUniqueSixKeyVector

------------------------------------------------------------------------
-- Reconstruction / held-out prediction firewall.
------------------------------------------------------------------------

data ReconstructionReceiptEqualsHeldOutPrediction : Set where

reconstructionReceiptDoesNotBecomeHeldOutPrediction :
  ReconstructionReceiptEqualsHeldOutPrediction → ⊥
reconstructionReceiptDoesNotBecomeHeldOutPrediction ()

daoRuntimeArtifactStillReconstructionOnly :
  DAORun.originalPaperManifestClaimed
    DAORun.canonicalDAOSameKeyReconstructionRunStatus
  ≡ false
daoRuntimeArtifactStillReconstructionOnly =
  DAORun.originalPaperManifestNotClaimed

quantitativePredictionBoundaryStillOpen :
  Prediction.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
quantitativePredictionBoundaryStillOpen = refl

sourceNonLocationStillOpen :
  BedroyaManifest.firstPartyPredecessorImplementationLocatedByCurrentSearch
    BedroyaManifest.canonicalBedroyaParameterManifestStatus
  ≡ false
sourceNonLocationStillOpen =
  BedroyaManifest.predecessorImplementationStillUnlocatedByCurrentSearch
