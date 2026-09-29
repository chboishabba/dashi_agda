{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.W4YMStressEnergyFromCurvatureSixExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Curvature
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureStressInsertionExact as Stress

------------------------------------------------------------------------
-- W4 YM STRESS-ENERGY COMPILER FROM A COORDINATE SIX-CURVATURE OBJECT
--
-- Once a source/Gate-3 curvature is mapped into the six independent
-- su(2)-valued components F01,F02,F03,F12,F13,F23, the Euclidean reference
-- metric contractions and the full symmetric YM stress tensor are no longer
-- separate obligations.  They are compiled by the exact curvature formulas.
--
-- This does NOT identify the older Gate-3 SFGC 2D witness with this side-4
-- curvature carrier and does NOT supply W4/Drell-Yan physical authority.
------------------------------------------------------------------------

record CoordinateYMCurvatureStress (Configuration : Set) : Set₁ where
  field
    curvature :
      Curvature.FiniteCurvatureSixFamily Configuration

open CoordinateYMCurvatureStress public

ymStressComponent :
  ∀ {Configuration} →
  CoordinateYMCurvatureStress Configuration →
  Configuration →
  K.SymmetricTensorComponent4 →
  ℚ
ymStressComponent dataSet configuration component =
  Stress.stressInsertion
    (Curvature.curvatureAt (curvature dataSet) configuration)
    component

ymStressTrace :
  ∀ {Configuration} →
  CoordinateYMCurvatureStress Configuration →
  Configuration → ℚ
ymStressTrace dataSet configuration =
  Stress.classicalStressTrace
    (Curvature.curvatureAt (curvature dataSet) configuration)

ymStressTraceIsZero :
  ∀ {Configuration}
    (dataSet : CoordinateYMCurvatureStress Configuration)
    configuration →
  ymStressTrace dataSet configuration ≡ 0ℚ
ymStressTraceIsZero dataSet configuration =
  Stress.classicalStressTraceIsZero
    (Curvature.curvatureAt (curvature dataSet) configuration)

data W4YMCurvatureCompilerResolved : Set where
  coordinateFieldStrengthAvailable :
    W4YMCurvatureCompilerResolved

  euclideanMetricRaisingLoweringCompiled :
    W4YMCurvatureCompilerResolved

  singleContractionCompiled :
    W4YMCurvatureCompilerResolved

  doubleContractionCompiled :
    W4YMCurvatureCompilerResolved

  oneQuarterScalarAlgebraCompiled :
    W4YMCurvatureCompilerResolved

  su2TraceInnerProductCompiled :
    W4YMCurvatureCompilerResolved

canonicalResolved :
  List W4YMCurvatureCompilerResolved
canonicalResolved =
  coordinateFieldStrengthAvailable
  ∷ euclideanMetricRaisingLoweringCompiled
  ∷ singleContractionCompiled
  ∷ doubleContractionCompiled
  ∷ oneQuarterScalarAlgebraCompiled
  ∷ su2TraceInnerProductCompiled
  ∷ []

data W4YMCurvatureCompilerOpen : Set where
  gate3SFGCToCurvatureSixSameObject :
    W4YMCurvatureCompilerOpen

  authorityBackedW4MatterStressEnergyInterface :
    W4YMCurvatureCompilerOpen

canonicalOpen :
  List W4YMCurvatureCompilerOpen
canonicalOpen =
  gate3SFGCToCurvatureSixSameObject
  ∷ authorityBackedW4MatterStressEnergyInterface
  ∷ []

coordinateYMTensorConstructedFromCurvatureSix : Bool
coordinateYMTensorConstructedFromCurvatureSix = true

coordinateYMTensorConstructedFromCurvatureSixIsTrue :
  coordinateYMTensorConstructedFromCurvatureSix ≡ true
coordinateYMTensorConstructedFromCurvatureSixIsTrue = refl

gate3SameObjectMapStillRequired : Bool
gate3SameObjectMapStillRequired = true

gate3SameObjectMapStillRequiredIsTrue :
  gate3SameObjectMapStillRequired ≡ true
gate3SameObjectMapStillRequiredIsTrue = refl

drellYanOrW4AuthorityStillRequired : Bool
drellYanOrW4AuthorityStillRequired = true

drellYanOrW4AuthorityStillRequiredIsTrue :
  drellYanOrW4AuthorityStillRequired ≡ true
drellYanOrW4AuthorityStillRequiredIsTrue = refl
