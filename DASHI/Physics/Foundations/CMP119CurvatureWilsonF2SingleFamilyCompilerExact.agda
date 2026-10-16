{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CurvatureWilsonF2SingleFamilyCompilerExact where

------------------------------------------------------------------------
-- ONE FINITE CURVATURE FAMILY FOR CLASSICAL DS AND ANOMALY F^2
--
-- The Wilson/Gibbs ten-slot compiler and the finite SU(2) trace/anomaly lane
-- both consume the repository's exact `FiniteCurvatureSixFamily` carrier.
-- Do not select a second finite curvature/F^2 family: the anomaly observable is
-- computed from the SAME curvature object that already determines all ten
-- classical action metric variations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Curvature
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119CurvatureWilsonSelectedInsertionCompilerExact as Selected
import DASHI.Physics.Foundations.CMP119AntigravityCurvatureF2PositivityExact as F2

asFiniteCurvatureF2Family :
  ∀ {Configuration} →
  Curvature.FiniteCurvatureSixFamily Configuration →
  F2.FiniteCurvatureF2Family Configuration
asFiniteCurvatureF2Family family = record
  { F2.FiniteCurvatureF2Family.curvature = family
  }

f2FamilyUsesExactSameCurvature :
  ∀ {Configuration}
    (family : Curvature.FiniteCurvatureSixFamily Configuration) →
  F2.curvature (asFiniteCurvatureF2Family family) ≡ family
f2FamilyUsesExactSameCurvature family = refl

record CurvatureWilsonF2Source (Configuration : Set) : Set₁ where
  field
    curvatureFamily : Curvature.FiniteCurvatureSixFamily Configuration
    insertionObservable : Configuration → ℚ
    insertionVariation :
      K.SymmetricTensorComponent4 → Configuration → ℚ

open CurvatureWilsonF2Source public

asCurvatureSelectedInsertion :
  ∀ {Configuration} →
  CurvatureWilsonF2Source Configuration →
  Selected.CurvatureSelectedInsertion Configuration
asCurvatureSelectedInsertion source = record
  { Selected.CurvatureSelectedInsertion.curvatureFamily =
      curvatureFamily source
  ; Selected.CurvatureSelectedInsertion.insertionObservable =
      insertionObservable source
  ; Selected.CurvatureSelectedInsertion.insertionVariation =
      insertionVariation source
  }

asClassicalWilsonSelectedInsertion :
  ∀ {Configuration} →
  CurvatureWilsonF2Source Configuration →
  Wilson.ClassicalWilsonSelectedInsertion Configuration
asClassicalWilsonSelectedInsertion source =
  Selected.asClassicalWilsonSelectedInsertion
    (asCurvatureSelectedInsertion source)

asFiniteF2Family :
  ∀ {Configuration} →
  CurvatureWilsonF2Source Configuration →
  F2.FiniteCurvatureF2Family Configuration
asFiniteF2Family source =
  asFiniteCurvatureF2Family (curvatureFamily source)

wilsonActionVariationUsesSourceCurvature :
  ∀ {Configuration}
    (source : CurvatureWilsonF2Source Configuration)
    configuration component →
  Wilson.actionVariationAt
    (Wilson.actionMetricVariation
      (asClassicalWilsonSelectedInsertion source))
    component configuration
  ≡
  Curvature.actionVariation
    (Curvature.curvatureAt
      (curvatureFamily source) configuration)
    component
wilsonActionVariationUsesSourceCurvature source configuration component =
  Selected.compiledActionVariationIsCurvatureFormula
    (asCurvatureSelectedInsertion source) configuration component

f2ObservableUsesSourceCurvature :
  ∀ {Configuration}
    (source : CurvatureWilsonF2Source Configuration)
    configuration →
  F2.fieldStrengthSquare (asFiniteF2Family source) configuration
  ≡
  F2.normalizedCurvatureF2
    (Curvature.curvatureAt
      (curvatureFamily source) configuration)
f2ObservableUsesSourceCurvature source configuration = refl

f2ObservablePointwiseNonnegative :
  ∀ {Configuration}
    (source : CurvatureWilsonF2Source Configuration)
    configuration →
  0ℚ ≤ F2.fieldStrengthSquare (asFiniteF2Family source) configuration
f2ObservablePointwiseNonnegative source =
  F2.fieldStrengthSquareNonnegative (asFiniteF2Family source)

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

independentFiniteF2CurvatureFamilyRequired : Bool
independentFiniteF2CurvatureFamilyRequired = false

sameCurvatureFamilyPaysWilsonTenSlotDSAndF2 : Bool
sameCurvatureFamilyPaysWilsonTenSlotDSAndF2 = true

f2PointwiseNonnegativityNeedsNewPhysics : Bool
f2PointwiseNonnegativityNeedsNewPhysics = false

-- Strict positivity is stronger than nonnegativity and still requires a
-- selected nonzero-curvature witness (or the corresponding real/Haar support
-- theorem on the preferred continuum route).
strictF2PositivityStillNeedsSelectedNonzeroCurvatureWitness : Bool
strictF2PositivityStillNeedsSelectedNonzeroCurvatureWitness = true
