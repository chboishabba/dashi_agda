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
--
-- Shared observable identity and concrete DESI observation keys are now paid.
-- What remains is model execution: both hypotheses must be run/derived onto the
-- same future BAO keys before a numerical residual is well typed.
--
-- The two lanes are currently asymmetric:
--   * DAO/DRMD has a public CLASS implementation and an LSS-independent
--     parameter target from arXiv:2602.23895;
--   * the Bedroya-Obied-Vafa-Wu evolving Dark-Dimension paper supplies the
--     model equations and retrospective fit, but no first-party public
--     executable implementation was located in this acquisition tranche.
--
-- LSS-independent inference is not promoted to chronological holdout or
-- preregistration.  It can strengthen a derivation chain without paying the
-- future-data discipline owned by GRQuantumPredictionProtocol.
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
    "public CLASS implementation of the Dark Radiation-Matter Decoupling model; executable availability does not by itself supply the frozen same-key BAO prediction vector required here"
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
-- Debt carrier.
------------------------------------------------------------------------

record SameKeyPredictionDerivationDebt : Set where
  constructor sameKeyPredictionDerivationDebt
  field
    sharedBAOObservableLocated : Bool
    sameDESIObservationKeyLocated : Bool

    daoExecutableModelLocated : Bool
    darkDimensionExecutableModelLocated : Bool

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
-- A concrete same-key request object.  It names the key and both source lanes
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
