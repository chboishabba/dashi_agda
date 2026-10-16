{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974ModelCredibilityValidationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedModelFibreExact as Model
import DASHI.Physics.Propulsion.Rocketdyne1974ThermalModelValidationExact as Therm

------------------------------------------------------------------------
-- TEST-052 MODEL-CREDIBILITY FRONTIER
--
-- R-9557 source-pays a historical prediction/measurement comparison, but the
-- numerical residual, uncertainty model and equations are not recovered.
-- NASA-STD-7009B / NASA-HDBK-7009B are contemporary credibility comparators:
-- they motivate explicit verification, validation, uncertainty and declared
-- use domains, but they do not retroactively impose requirements on R-9557.
------------------------------------------------------------------------

genericModelBoundary : Model.ConsumerIndexedModelBoundary
genericModelBoundary = Model.canonicalConsumerIndexedModelBoundary

test052SourceReportedValidationReceipt : Model.EmpiricalValidationReceipt
test052SourceReportedValidationReceipt = Model.empirical-validation-receipt
  String String String
  "R-9557 predicted Test-052 isotherm / temperature-history object"
  "R-9557 measured baseline engine temperatures"
  "source-reported graphical/model-test correlation; exact numerical residual not recovered"
  "NASA-CR-140308 / Rocketdyne R-9557, Test 052 / Figs. 91-92 context"

record Test052CredibilityFrontier : Set where
  constructor test052-credibility-frontier
  field
    reportedCorrelationPaid : Bool
    numericalValidationResidualPaid : Bool
    validationCriterionRecovered : Bool
    modelEquationAndDiscretizationPaid : Bool
    solverVerificationPaid : Bool
    measurementUncertaintyPaid : Bool
    modelFormUncertaintyPaid : Bool
    propagatedPredictionUncertaintyPaid : Bool
    offDesignValidationPaid : Bool
    test768PredictionFrozenBeforeOutcomeUse : Bool
    test8702PredictionFrozenBeforeOutcomeUse : Bool
    modern7009AppliesRetroactively : Bool
    sourceReference : String
    stoppingRule : String

test052CredibilityFrontier : Test052CredibilityFrontier
test052CredibilityFrontier = test052-credibility-frontier
  true
  false false false false false false false false false false
  false
  "R-9557 Test-052 correlation; NASA-STD-7009B (2024) and NASA-HDBK-7009B (2026) as contemporary model-credibility comparators only"
  "Recover equations/discretization, Test-052 numerical predictions and measurements, comparison criterion and uncertainty; validate there before freezing one model family for Test 768 and Test 870-2."

sourceReportedCorrelationPaid : Bool
sourceReportedCorrelationPaid = Therm.sourceValidatedThermalModelExists

numericalValidationErrorUnpaid : Bool
numericalValidationErrorUnpaid = true

uncertaintyPropagationUnpaid : Bool
uncertaintyPropagationUnpaid = true

offDesignPredictionUnpaid : Bool
offDesignPredictionUnpaid = true

sameModelTwoRunValidationTarget : String
sameModelTwoRunValidationTarget =
  "After Test-052 calibration/validation is frozen, the SAME thermo-structural model family must predict Haynes-25 Test 768 damage and WC103/VH-101 Test 870-2 observed-run survival using documented article differences only."

modern7009DoesNotCreateHistoricalValidation : Bool
modern7009DoesNotCreateHistoricalValidation = true
