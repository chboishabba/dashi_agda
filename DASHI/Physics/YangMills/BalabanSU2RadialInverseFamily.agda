module DASHI.Physics.YangMills.BalabanSU2RadialInverseFamily where

------------------------------------------------------------------------
-- Uniform inverse family for radial reduced SU(2) adjoint operators.
--
-- The preceding modules reduce every conjugation-equivariant function of
-- ad_Y to three radial scalar coefficients and identify the exact three scalar
-- equations required for a pointwise inverse.  This module packages those
-- equations uniformly in r = <Y,Y> and exposes the resulting cancellation
-- theorems at the concrete su(2) carrier.
--
-- This is the intended theorem socket for the source functions customarily
-- written g(+i ad_Y), g(-i ad_Y), and their inverses.  No analytic function or
-- estimate is assumed here: an eventual source-specific instance must provide
-- the coefficient functions and prove the three equations for every radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra )
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator using
  ( RadialReducedOperator
  ; applyRadialReduced
  ; radialInvariant
  )
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointInverse using
  ( RadialInverseAt
  ; applyRadialInverse
  )

record RadialInverseFamily
  (forward inverse : RadialReducedOperator) : Set₁ where
  field
    inverseAt : ∀ radius → RadialInverseAt forward inverse radius

open RadialInverseFamily public

applyRadialInverseFamily :
  ∀ {forward inverse} →
  RadialInverseFamily forward inverse →
  (Y X : SU2LieAlgebra) →
  applyRadialReduced forward Y
    (applyRadialReduced inverse Y X)
  ≡ X
applyRadialInverseFamily family Y X =
  applyRadialInverse
    _ _ Y X
    (inverseAt family (radialInvariant Y))

record TwoSidedRadialInverseFamily
  (forward inverse : RadialReducedOperator) : Set₁ where
  field
    forwardAfterInverse : RadialInverseFamily forward inverse
    inverseAfterForward : RadialInverseFamily inverse forward

open TwoSidedRadialInverseFamily public

cancelForwardAfterInverse :
  ∀ {forward inverse} →
  TwoSidedRadialInverseFamily forward inverse →
  (Y X : SU2LieAlgebra) →
  applyRadialReduced forward Y
    (applyRadialReduced inverse Y X)
  ≡ X
cancelForwardAfterInverse family =
  applyRadialInverseFamily (forwardAfterInverse family)

cancelInverseAfterForward :
  ∀ {forward inverse} →
  TwoSidedRadialInverseFamily forward inverse →
  (Y X : SU2LieAlgebra) →
  applyRadialReduced inverse Y
    (applyRadialReduced forward Y X)
  ≡ X
cancelInverseAfterForward family =
  applyRadialInverseFamily (inverseAfterForward family)

record SignedRadialInversePair : Set₁ where
  field
    plus : RadialReducedOperator
    plusInverse : RadialReducedOperator
    minus : RadialReducedOperator
    minusInverse : RadialReducedOperator

    plusTwoSided : TwoSidedRadialInverseFamily plus plusInverse
    minusTwoSided : TwoSidedRadialInverseFamily minus minusInverse

open SignedRadialInversePair public

cancelPlusForwardAfterInverse :
  (family : SignedRadialInversePair) →
  (Y X : SU2LieAlgebra) →
  applyRadialReduced (plus family) Y
    (applyRadialReduced (plusInverse family) Y X)
  ≡ X
cancelPlusForwardAfterInverse family =
  cancelForwardAfterInverse (plusTwoSided family)

cancelPlusInverseAfterForward :
  (family : SignedRadialInversePair) →
  (Y X : SU2LieAlgebra) →
  applyRadialReduced (plusInverse family) Y
    (applyRadialReduced (plus family) Y X)
  ≡ X
cancelPlusInverseAfterForward family =
  cancelInverseAfterForward (plusTwoSided family)

cancelMinusForwardAfterInverse :
  (family : SignedRadialInversePair) →
  (Y X : SU2LieAlgebra) →
  applyRadialReduced (minus family) Y
    (applyRadialReduced (minusInverse family) Y X)
  ≡ X
cancelMinusForwardAfterInverse family =
  cancelForwardAfterInverse (minusTwoSided family)

cancelMinusInverseAfterForward :
  (family : SignedRadialInversePair) →
  (Y X : SU2LieAlgebra) →
  applyRadialReduced (minusInverse family) Y
    (applyRadialReduced (minus family) Y X)
  ≡ X
cancelMinusInverseAfterForward family =
  cancelInverseAfterForward (minusTwoSided family)
