module DASHI.Empirical.DarkDimensionSameKeyPredictionDebtExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Empirical.DarkDimensionSharedBAOObservableExact as SharedBAO
import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey

------------------------------------------------------------------------
-- SAME-KEY MODEL-PREDICTION DERIVATION DEBT
------------------------------------------------------------------------

daoIndependentTargetSource : Source.AttributedSource
daoIndependentTargetSource =
  Source.mkNoDOISource
    "Mathias Garny; Florian Niedermann; Martin S. Sloth"
    "Dark Acoustic Oscillations and the Hubble Tension"
    "arXiv:2602.23895"
    "2026"
    "https://arxiv.org/abs/2602.23895"
    Source.academicArticleSource
    "source for an inference independent of large-scale-structure data giving a concrete DAO sound-horizon/amplitude target; independence from LSS does not imply chronological preregistration before DESI DR2"
    Source.publicAttribution

daoDRMDClassSource : Source.AttributedSource
daoDRMDClassSource =
  Source.mkNoDOISource
    "NEDE-Cosmo collaboration repository"
    "DRMD-CLASS"
    "GitHub public source repository"
    "2026"
    "https://github.com/NEDE-Cosmo/DRMD-CLASS"
    Source.practitionerSource
    "public CLASS implementation of the Dark Radiation-Matter Decoupling model; revision/config provenance is pinned below, but no DASHI execution receipt or same-key BAO prediction is imported by source existence"
    Source.publicAttribution

darkDimensionModelSource : Source.AttributedSource
darkDimensionModelSource =
  Source.mkNoDOISource
    "Alek Bedroya; Georges Obied; Cumrun Vafa; David H. Wu"
    "Evolving Dark Sector and the Dark Dimension Scenario"
    "arXiv:2507.03090 / Physical Review D accepted 2026"
    "2026"
    "https://arxiv.org/abs/2507.03090"
    Source.academicArticleSource
    "source for the evolving Dark-Dimension equations and DESI DR2 retrospective fit; no first-party public executable implementation is admitted by this tranche"
    Source.publicAttribution

------------------------------------------------------------------------
-- Revision-pinned public execution surface for the DAO/DRMD lane.
------------------------------------------------------------------------

record PublicExecutionSurface : Set where
  constructor publicExecutionSurface
  field
    repositoryLabel : String
    revision : String
    primaryInputSurface : String
    inferenceConfigSurface : String
    derivedObservableSurface : String
    executableRevisionPinned : Bool
    executionConfigSurfaceLocated : Bool
    executedByDASHI : Bool

open PublicExecutionSurface public

daoDRMDExecutionSurface : PublicExecutionSurface
daoDRMDExecutionSurface =
  publicExecutionSurface
    "NEDE-Cosmo/DRMD-CLASS"
    "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9"
    "DRMD.ini"
    "cobaya/"
    "rs_d_drmd"
    true
    true
    false

daoDRMDClassRevision : String
daoDRMDClassRevision = "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9"

------------------------------------------------------------------------
-- Debt carrier.
------------------------------------------------------------------------

record SameKeyPredictionDerivationDebt : Set where
  constructor sameKeyPredictionDerivationDebt
  field
    sharedBAOObservableLocated : Bool
    sameDESIObservationKeyLocated : Bool

    daoExecutableModelLocated : Bool
    darkDimensionExecutableModelLocated : Bool
    daoExecutableRevisionPinned : Bool
    daoExecutionConfigSurfaceLocated : Bool
    daoExecutedByDASHI : Bool

    daoLargeScaleStructureIndependentTargetLocated : Bool
    daoTargetChronologicallyHeldOutBeforeDESIDR2 : Bool

    daoSameKeyBAOVectorDerived : Bool
    darkDimensionSameKeyBAOVectorDerived : Bool

    commonCovarianceSurfaceAssembled : Bool
    analysisChoicesFrozenBeforeFutureData : Bool
    sameKeyLikelihoodLocked : Bool
    debtClosed : Bool

open SameKeyPredictionDerivationDebt public

canonicalSameKeyPredictionDerivationDebt : SameKeyPredictionDerivationDebt
canonicalSameKeyPredictionDerivationDebt =
  sameKeyPredictionDerivationDebt
    true
    true
    true
    false
    true
    true
    false
    true
    false
    false
    false
    false
    false
    false
    false

sameKeyPredictionDebtStillOpen :
  debtClosed canonicalSameKeyPredictionDerivationDebt ≡ false
sameKeyPredictionDebtStillOpen = refl

sharedBAONumericalSeparationStillBlocked :
  SharedBAO.sharedObservableNumericalSeparationLocked
    SharedBAO.canonicalSharedBAOStatus
  ≡ false
sharedBAONumericalSeparationStillBlocked =
  SharedBAO.sharedObservableNumericalPredictionsStillOpen

------------------------------------------------------------------------
-- WrongType boundary: LSS independence != chronological holdout.
------------------------------------------------------------------------

data LargeScaleStructureIndependenceImpliesChronologicalHoldout : Set where

largeScaleStructureIndependentDoesNotMeanChronologicallyHeldOut :
  LargeScaleStructureIndependenceImpliesChronologicalHoldout → ⊥
largeScaleStructureIndependentDoesNotMeanChronologicallyHeldOut ()

------------------------------------------------------------------------
-- Concrete same-key request objects.  They name the key and both source lanes
-- without supplying fabricated predictions.
------------------------------------------------------------------------

record SameKeyPredictionRequest : Set where
  constructor sameKeyPredictionRequest
  field
    key : ObservationKey.SharedBAOObservationKey
    darkDimensionSource : Source.AttributedSource
    daoSource : Source.AttributedSource
    darkDimensionPredictionPresent : Bool
    daoPredictionPresent : Bool
    comparisonLocked : Bool

open SameKeyPredictionRequest public

lrg1TransversePredictionRequest : SameKeyPredictionRequest
lrg1TransversePredictionRequest =
  sameKeyPredictionRequest
    ObservationKey.lrg1TransverseKey
    darkDimensionModelSource
    daoIndependentTargetSource
    false
    false
    false

lrg1RadialPredictionRequest : SameKeyPredictionRequest
lrg1RadialPredictionRequest =
  sameKeyPredictionRequest
    ObservationKey.lrg1RadialKey
    darkDimensionModelSource
    daoIndependentTargetSource
    false
    false
    false

bedroyaArXiv : String
bedroyaArXiv = "2507.03090"

daoIndependentTargetArXiv : String
daoIndependentTargetArXiv = "2602.23895"

daoExecutableRepository : String
daoExecutableRepository = "DRMD-CLASS"
