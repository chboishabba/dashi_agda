{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalWilsonDiagonalMetricVariationExact as Diag
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Ten
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact as Curl

------------------------------------------------------------------------
-- FULL CLASSICAL d=4 METRIC VARIATION FROM SIX CURVATURE COMPONENTS
--
-- Write the six independent su(2)-valued curvature components as
--
--   F01 F02 F03 F12 F13 F23.
--
-- Normalize orientation energies as E_ab = 1/2 <F_ab,F_ab>.  The diagonal
-- metric variations then coincide with the existing six-energy compiler.
--
-- For an independent symmetric off-diagonal perturbation h_ab,
--
--   DS_ab = - sum_rho <F_a rho, F_b rho>.
--
-- Antisymmetry F_ba = -F_ab fixes all signs below.
------------------------------------------------------------------------

half : ℚ
half = + 1 / 2

record CurvatureSix : Set where
  field
    f01 f02 f03 f12 f13 f23 : Curl.RationalVector3

open CurvatureSix public

energy : Curl.RationalVector3 → ℚ
energy value = half * Curl.vectorDot value value

orientationEnergies :
  CurvatureSix → Diag.SixPlaquetteOrientationEnergies
orientationEnergies curvature = record
  { Diag.SixPlaquetteOrientationEnergies.e01 = energy (f01 curvature)
  ; Diag.SixPlaquetteOrientationEnergies.e02 = energy (f02 curvature)
  ; Diag.SixPlaquetteOrientationEnergies.e03 = energy (f03 curvature)
  ; Diag.SixPlaquetteOrientationEnergies.e12 = energy (f12 curvature)
  ; Diag.SixPlaquetteOrientationEnergies.e13 = energy (f13 curvature)
  ; Diag.SixPlaquetteOrientationEnergies.e23 = energy (f23 curvature)
  }

k01 k02 k03 k12 k13 k23 : CurvatureSix → ℚ
k01 curvature =
  Curl.vectorDot (f02 curvature) (f12 curvature)
  + Curl.vectorDot (f03 curvature) (f13 curvature)

k02 curvature =
  - Curl.vectorDot (f01 curvature) (f12 curvature)
  + Curl.vectorDot (f03 curvature) (f23 curvature)

k03 curvature =
  - Curl.vectorDot (f01 curvature) (f13 curvature)
  - Curl.vectorDot (f02 curvature) (f23 curvature)

k12 curvature =
  Curl.vectorDot (f01 curvature) (f02 curvature)
  + Curl.vectorDot (f13 curvature) (f23 curvature)

k13 curvature =
  Curl.vectorDot (f01 curvature) (f03 curvature)
  - Curl.vectorDot (f12 curvature) (f23 curvature)

k23 curvature =
  Curl.vectorDot (f02 curvature) (f03 curvature)
  + Curl.vectorDot (f12 curvature) (f13 curvature)

mixedDS01 mixedDS02 mixedDS03 mixedDS12 mixedDS13 mixedDS23 :
  CurvatureSix → ℚ
mixedDS01 curvature = - k01 curvature
mixedDS02 curvature = - k02 curvature
mixedDS03 curvature = - k03 curvature
mixedDS12 curvature = - k12 curvature
mixedDS13 curvature = - k13 curvature
mixedDS23 curvature = - k23 curvature

actionVariation :
  CurvatureSix → K.SymmetricTensorComponent4 → ℚ
actionVariation curvature K.component00 =
  Diag.dS00 (orientationEnergies curvature)
actionVariation curvature K.component01 = mixedDS01 curvature
actionVariation curvature K.component02 = mixedDS02 curvature
actionVariation curvature K.component03 = mixedDS03 curvature
actionVariation curvature K.component11 =
  Diag.dS11 (orientationEnergies curvature)
actionVariation curvature K.component12 = mixedDS12 curvature
actionVariation curvature K.component13 = mixedDS13 curvature
actionVariation curvature K.component22 =
  Diag.dS22 (orientationEnergies curvature)
actionVariation curvature K.component23 = mixedDS23 curvature
actionVariation curvature K.component33 =
  Diag.dS33 (orientationEnergies curvature)

diagonalTraceZero :
  ∀ curvature →
  actionVariation curvature K.component00
  + actionVariation curvature K.component11
  + actionVariation curvature K.component22
  + actionVariation curvature K.component33
  ≡ 0ℚ
diagonalTraceZero curvature =
  Diag.classicalDiagonalMetricTraceIsZero (orientationEnergies curvature)

record FiniteCurvatureSixFamily (Configuration : Set) : Set₁ where
  field
    curvatureAt : Configuration → CurvatureSix

open FiniteCurvatureSixFamily public

asClassicalWilsonTenMetricVariation :
  ∀ {Configuration} →
  FiniteCurvatureSixFamily Configuration →
  Ten.ClassicalWilsonTenMetricVariation Configuration
asClassicalWilsonTenMetricVariation family = record
  { Ten.ClassicalWilsonTenMetricVariation.diagonalEnergies = record
      { Diag.FiniteSixPlaquetteEnergyFamily.orientationEnergies =
          λ configuration →
            orientationEnergies (curvatureAt family configuration)
      }
  ; Ten.ClassicalWilsonTenMetricVariation.mixed01 =
      λ configuration → mixedDS01 (curvatureAt family configuration)
  ; Ten.ClassicalWilsonTenMetricVariation.mixed02 =
      λ configuration → mixedDS02 (curvatureAt family configuration)
  ; Ten.ClassicalWilsonTenMetricVariation.mixed03 =
      λ configuration → mixedDS03 (curvatureAt family configuration)
  ; Ten.ClassicalWilsonTenMetricVariation.mixed12 =
      λ configuration → mixedDS12 (curvatureAt family configuration)
  ; Ten.ClassicalWilsonTenMetricVariation.mixed13 =
      λ configuration → mixedDS13 (curvatureAt family configuration)
  ; Ten.ClassicalWilsonTenMetricVariation.mixed23 =
      λ configuration → mixedDS23 (curvatureAt family configuration)
  }

tenActionVariationIsCurvatureFormula :
  ∀ {Configuration}
    (family : FiniteCurvatureSixFamily Configuration)
    configuration component →
  Ten.actionVariationAt
    (asClassicalWilsonTenMetricVariation family)
    component configuration
  ≡ actionVariation (curvatureAt family configuration) component
tenActionVariationIsCurvatureFormula family configuration K.component00 = refl
tenActionVariationIsCurvatureFormula family configuration K.component01 = refl
tenActionVariationIsCurvatureFormula family configuration K.component02 = refl
tenActionVariationIsCurvatureFormula family configuration K.component03 = refl
tenActionVariationIsCurvatureFormula family configuration K.component11 = refl
tenActionVariationIsCurvatureFormula family configuration K.component12 = refl
tenActionVariationIsCurvatureFormula family configuration K.component13 = refl
tenActionVariationIsCurvatureFormula family configuration K.component22 = refl
tenActionVariationIsCurvatureFormula family configuration K.component23 = refl
tenActionVariationIsCurvatureFormula family configuration K.component33 = refl
