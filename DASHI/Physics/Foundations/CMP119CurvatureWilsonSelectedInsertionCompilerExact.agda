{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CurvatureWilsonSelectedInsertionCompilerExact where

------------------------------------------------------------------------
-- CURVATURE -> CANONICAL WILSON/GIBBS SELECTED-INSERTION INPUT
--
-- `CMP119ClassicalCurvatureTenMetricVariationExact` already proves that one
-- CurvatureSix family determines all ten classical action metric variations.
-- The canonical Wilson/Gibbs selected-insertion package should therefore not
-- accept another independent ten-slot DS family once curvature is known.
--
-- What remains independent is exactly the selected insertion observable O and
-- its metric variation DO[h].  This module compiles those with CurvatureSix into
-- the existing `ClassicalWilsonSelectedInsertion` consumed by the selected
-- CMP119 Wilson/Gibbs same-object anchor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Curvature
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson

record CurvatureSelectedInsertion (Configuration : Set) : Set₁ where
  field
    curvatureFamily : Curvature.FiniteCurvatureSixFamily Configuration

    insertionObservable : Configuration → ℚ

    insertionVariation :
      K.SymmetricTensorComponent4 → Configuration → ℚ

open CurvatureSelectedInsertion public

asClassicalWilsonSelectedInsertion :
  ∀ {Configuration} →
  CurvatureSelectedInsertion Configuration →
  Wilson.ClassicalWilsonSelectedInsertion Configuration
asClassicalWilsonSelectedInsertion dataSet = record
  { Wilson.ClassicalWilsonSelectedInsertion.actionMetricVariation =
      Curvature.asClassicalWilsonTenMetricVariation
        (curvatureFamily dataSet)
  ; Wilson.ClassicalWilsonSelectedInsertion.insertionObservable =
      insertionObservable dataSet
  ; Wilson.ClassicalWilsonSelectedInsertion.insertionVariation =
      insertionVariation dataSet
  }

compiledActionVariationIsCurvatureFormula :
  ∀ {Configuration}
    (dataSet : CurvatureSelectedInsertion Configuration)
    configuration component →
  Wilson.actionVariationAt
    (Wilson.actionMetricVariation
      (asClassicalWilsonSelectedInsertion dataSet))
    component configuration
  ≡
  Curvature.actionVariation
    (Curvature.curvatureAt
      (curvatureFamily dataSet) configuration)
    component
compiledActionVariationIsCurvatureFormula dataSet configuration component =
  Curvature.tenActionVariationIsCurvatureFormula
    (curvatureFamily dataSet) configuration component

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

tenIndependentActionVariationCallbacksRequired : Bool
tenIndependentActionVariationCallbacksRequired = false

curvatureSixPaysWholeClassicalActionMetricVariation : Bool
curvatureSixPaysWholeClassicalActionMetricVariation = true

selectedInsertionObservableAndMetricVariationStillRequired : Bool
selectedInsertionObservableAndMetricVariationStillRequired = true

-- For the selected nonlinear CMP119 source, the remaining same-object physics
-- payment is to identify its finite configuration with the curvature family.
-- The literal side-four flat/tangent realization is already available, but is
-- not silently promoted to that nonlinear source.
selectedNonlinearCurvatureRealizationStillRequired : Bool
selectedNonlinearCurvatureRealizationStillRequired = true
