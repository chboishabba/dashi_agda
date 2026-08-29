module DASHI.Core.RobustExperimentInferenceFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Stage-7 frontier: realism, robustness and theory discrimination.
--
-- These are not claimed solved by Stage 6.  The purpose of this module is to
-- make the next obligations explicit and to prove one generic anti-pattern:
-- parameter fit does not determine model adequacy.
------------------------------------------------------------------------

data RobustnessObligation : Set where
  modelDiscrepancy : RobustnessObligation
  vectorStateParameterControl : RobustnessObligation
  correlatedUncertainty : RobustnessObligation
  experimentDesign : RobustnessObligation
  quantitativeLocalIdentifiability : RobustnessObligation
  heldOutRepairValidation : RobustnessObligation

------------------------------------------------------------------------
-- A tiny exact counterexample to "fit implies adequacy".
------------------------------------------------------------------------

data TwoModels : Set where
  adequateModel : TwoModels
  inadequateModel : TwoModels

fit : TwoModels → Bool
fit adequateModel = true
fit inadequateModel = true

adequate : TwoModels → Bool
adequate adequateModel = true
adequate inadequateModel = false

sameFitDifferentAdequacy :
  (fit adequateModel ≡ fit inadequateModel) ×
  ¬ (adequate adequateModel ≡ adequate inadequateModel)
sameFitDifferentAdequacy = refl , λ ()

------------------------------------------------------------------------
-- Model discrepancy is kept separate from measurement noise and parameter
-- uncertainty.  This record is only an interface; no stochastic semantics are
-- silently attached to any field.
------------------------------------------------------------------------

record DiscrepancyModel
    (Input Prediction Residual : Set) : Set₁ where
  constructor discrepancyModel
  field
    modelPrediction : Input → Prediction
    discrepancy : Input → Residual
    measurementNoise : Input → Residual

------------------------------------------------------------------------
-- Correlated propagation requires a genuinely joint covariance object.  A
-- list of marginal variances is therefore not, by itself, a correlated budget.
------------------------------------------------------------------------

record CorrelatedUncertaintyInterface
    (Input Output Covariance : Set) : Set₁ where
  constructor correlatedUncertaintyInterface
  field
    inputCovariance : Covariance
    propagatedCovariance : Covariance
    propagationReceipt : Set

------------------------------------------------------------------------
-- Experiment design is consumer-relative.  The criterion is declared
-- separately from the candidate experiment language, so an optimizer cannot
-- promote its own criterion into scientific authority.
------------------------------------------------------------------------

record ExperimentDesign
    (Experiment Criterion : Set) : Set₁ where
  constructor experimentDesign
  field
    score : Experiment → Criterion
    Preferred : Experiment → Experiment → Set
    criterionJustification : Set

------------------------------------------------------------------------
-- Repairs must expose a held-out test surface before they can gain support.
------------------------------------------------------------------------

record HeldOutRepair
    (Repair Training HeldOut Prediction : Set) : Set₁ where
  constructor heldOutRepair
  field
    fitTraining : Repair → Training → Set
    predictHeldOut : Repair → HeldOut → Prediction
    heldOutDiscriminationReceipt : Set

------------------------------------------------------------------------
-- Boundary: Stage 6 does not discharge these merely by possessing calibrated
-- inference machinery.
------------------------------------------------------------------------

record RobustExperimentFrontierBoundary : Set where
  constructor robustExperimentFrontierBoundary
  field
    calibratedFitDeterminesModelAdequacy : Bool
    calibratedFitDeterminesModelAdequacyIsFalse :
      calibratedFitDeterminesModelAdequacy ≡ false

    diagonalVarianceBudgetSolvesCorrelatedAttribution : Bool
    diagonalVarianceBudgetSolvesCorrelatedAttributionIsFalse :
      diagonalVarianceBudgetSolvesCorrelatedAttribution ≡ false

    localJacobianRankGivesGlobalIdentifiability : Bool
    localJacobianRankGivesGlobalIdentifiabilityIsFalse :
      localJacobianRankGivesGlobalIdentifiability ≡ false

    repairThatFitsTrainingIsScientificallySupported : Bool
    repairThatFitsTrainingIsScientificallySupportedIsFalse :
      repairThatFitsTrainingIsScientificallySupported ≡ false

canonicalRobustExperimentFrontierBoundary : RobustExperimentFrontierBoundary
canonicalRobustExperimentFrontierBoundary =
  robustExperimentFrontierBoundary
    false refl
    false refl
    false refl
    false refl
