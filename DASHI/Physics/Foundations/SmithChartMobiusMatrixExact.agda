module DASHI.Physics.Foundations.SmithChartMobiusMatrixExact where

------------------------------------------------------------------------
-- SMITH CHART AS A GENUINE FRACTIONAL-LINEAR / MOBIUS COORDINATE
--
-- Existing owner:
--
--   Gamma(z) = (z - 1) / (z + 1)
--
-- This module exposes the exact 2x2 coefficient matrices:
--
--          [ 1  -1 ]
--   G  =   [ 1   1 ]
--
-- and normalized admittance
--
--          [ 0   1 ]
--   A  =   [ 1   0 ] ,
--
-- interpreted by
--
--   M[z] = (a z + b) / (c z + d).
--
-- The goal is structural, not terminological: this is the actual
-- fractional-linear geometry behind the Smith chart.  It remains distinct
-- from the modular j-invariant and from any modular-group action unless a
-- separate same-object/action theorem is supplied.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import DASHI.Physics.Foundations.SmithChartComplexReflectionExact as Smith

record MobiusMatrix (F : Smith.SmithComplexField) : Set where
  constructor mobius-matrix
  field
    a b c d : Smith.C F

open MobiusMatrix public

mobiusEvaluate :
  (F : Smith.SmithComplexField) →
  MobiusMatrix F →
  Smith.C F →
  Smith.C F
mobiusEvaluate F M z =
  Smith.div F
    (Smith.add F
      (Smith.mul F (a M) z)
      (b M))
    (Smith.add F
      (Smith.mul F (c M) z)
      (d M))

smithGammaMatrix :
  (F : Smith.SmithComplexField) →
  MobiusMatrix F
smithGammaMatrix F =
  mobius-matrix
    (Smith.one F)
    (Smith.neg F (Smith.one F))
    (Smith.one F)
    (Smith.one F)

normalizedAdmittanceMatrix :
  (F : Smith.SmithComplexField) →
  MobiusMatrix F
normalizedAdmittanceMatrix F =
  mobius-matrix
    (Smith.zero F)
    (Smith.one F)
    (Smith.one F)
    (Smith.zero F)

------------------------------------------------------------------------
-- Minimal algebra needed to identify the matrix formula with the already
-- existing Smith definitions.  We deliberately do not inflate
-- SmithComplexField into a full field hierarchy here.
------------------------------------------------------------------------

record SmithMobiusMatrixLaws
    (F : Smith.SmithComplexField) : Set₁ where
  field
    oneMul :
      (z : Smith.C F) →
      Smith.mul F (Smith.one F) z ≡ z

    zeroMul :
      (z : Smith.C F) →
      Smith.mul F (Smith.zero F) z ≡ Smith.zero F

    addZeroLeft :
      (z : Smith.C F) →
      Smith.add F (Smith.zero F) z ≡ z

    addZeroRight :
      (z : Smith.C F) →
      Smith.add F z (Smith.zero F) ≡ z

    addNegOneIsSubOne :
      (z : Smith.C F) →
      Smith.add F z (Smith.neg F (Smith.one F))
      ≡
      Smith.sub F z (Smith.one F)

    reciprocalIsOneDiv :
      (z : Smith.C F) →
      Smith.div F (Smith.one F) z
      ≡
      Smith.reciprocal F z

open SmithMobiusMatrixLaws public

------------------------------------------------------------------------
-- Smith Gamma is literally the [1 -1; 1 1] Mobius coordinate.
------------------------------------------------------------------------

smithGammaIsMobius :
  ∀ {F} →
  (L : SmithMobiusMatrixLaws F) →
  (z : Smith.C F) →
  mobiusEvaluate F (smithGammaMatrix F) z
  ≡
  Smith.normalizedReflection F z
smithGammaIsMobius {F} L z
  rewrite oneMul L z
        | addNegOneIsSubOne L z
        | oneMul L z
  = refl

------------------------------------------------------------------------
-- Normalized admittance is literally the [0 1; 1 0] Mobius involution.
------------------------------------------------------------------------

normalizedAdmittanceIsMobius :
  ∀ {F} →
  (L : SmithMobiusMatrixLaws F) →
  (z : Smith.C F) →
  mobiusEvaluate F (normalizedAdmittanceMatrix F) z
  ≡
  Smith.normalizedAdmittance F z
normalizedAdmittanceIsMobius {F} L z
  rewrite zeroMul L z
        | addZeroLeft L (Smith.one F)
        | oneMul L z
        | addZeroRight L z
        | reciprocalIsOneDiv L z
  = refl

------------------------------------------------------------------------
-- Existing Smith theorem, now read as matrix-induced half-turn on Gamma.
------------------------------------------------------------------------

smithAdmittanceMobiusActsAsGammaHalfTurn :
  ∀ {F} →
  (L : SmithMobiusMatrixLaws F) →
  (z : Smith.C F) →
  Smith.normalizedReflection F
    (mobiusEvaluate F (normalizedAdmittanceMatrix F) z)
  ≡
  Smith.neg F
    (Smith.normalizedReflection F z)
smithAdmittanceMobiusActsAsGammaHalfTurn {F} L z
  rewrite normalizedAdmittanceIsMobius L z
  =
  Smith.smithAdmittanceRotatesReflectionByHalfTurn F z

------------------------------------------------------------------------
-- Compact boundary.
------------------------------------------------------------------------

record SmithMobiusMatrixBoundary : Set where
  constructor smith-mobius-matrix-boundary
  field
    gammaMatrixIsOneMinusOneOneOne : Bool
    admittanceMatrixIsZeroOneOneZero : Bool
    smithGammaMobiusCompilerOwned : Bool
    normalizedAdmittanceMobiusCompilerOwned : Bool
    admittanceMatrixInducesGammaHalfTurn : Bool

    matrixLawsInhabitedHere : Bool
    smithMobiusMatrixIdentifiedWithModularJ : Bool
    smithAdmittanceMatrixIdentifiedWithModularT : Bool
    smithAdmittanceMatrixIdentifiedWithModularReflection : Bool

canonicalSmithMobiusMatrixBoundary :
  SmithMobiusMatrixBoundary
canonicalSmithMobiusMatrixBoundary =
  smith-mobius-matrix-boundary
    true true true true true
    false false false false
