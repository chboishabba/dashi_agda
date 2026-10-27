{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBackgroundMinimizerSymmetryNaturalityExact where

------------------------------------------------------------------------
-- NEW MATH FOR S1: SYMMETRY NATURALITY FROM THE VARIATIONAL MINIMIZER.
--
-- Bałaban's background field is characterized as the unique constrained
-- regular-gauge action minimizer.  Therefore its covariance under an
-- involutive lattice symmetry is not an independent source axiom.
--
-- If one generator preserves
--   * the coarse/fine constraint,
--   * regular gauge,
--   * the action,
-- and the action order is antisymmetric, then the transformed minimizer and
-- the minimizer of the transformed coarse field are feasible minimizers with
-- equal action.  Uniqueness gives the desired same-object equality.
--
-- This is exactly the hypercubic/B4 mechanism needed by the preferred CMP109/
-- 116 source path.  The remaining physical payment is finite-lattice
-- invariance of the selected action/constraint/gauge under each generator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as V

record InvolutiveVariationalSymmetry
    {CoarseField FineField Bond Bound : Set}
    (theorem : V.BackgroundFieldVariationalTheorem
      CoarseField FineField Bond Bound) : Set₁ where
  field
    actCoarse : CoarseField → CoarseField
    actFine : FineField → FineField

    actCoarseInvolutive : ∀ coarse → actCoarse (actCoarse coarse) ≡ coarse
    actFineInvolutive : ∀ fine → actFine (actFine fine) ≡ fine

    smallPreserved : ∀ coarse →
      V.CoarseSmallField theorem coarse →
      V.CoarseSmallField theorem (actCoarse coarse)

    constraintPreserved : ∀ {coarse fine} →
      V.FineConstraint theorem coarse fine →
      V.FineConstraint theorem (actCoarse coarse) (actFine fine)

    regularGaugePreserved : ∀ {fine} →
      V.FineRegularGauge theorem fine →
      V.FineRegularGauge theorem (actFine fine)

    actionInvariant : ∀ fine →
      V.action theorem (actFine fine) ≡ V.action theorem fine

    orderAntisymmetric : ∀ {left right} →
      V.LessEqual theorem left right →
      V.LessEqual theorem right left →
      left ≡ right

open InvolutiveVariationalSymmetry public

transformedSelectedBackgroundSatisfiesConstraint :
  ∀ {CoarseField FineField Bond Bound}
    {theorem : V.BackgroundFieldVariationalTheorem
      CoarseField FineField Bond Bound}
    (symmetry : InvolutiveVariationalSymmetry theorem)
    coarse
    (small : V.CoarseSmallField theorem coarse) →
  V.FineConstraint theorem
    (actCoarse symmetry coarse)
    (actFine symmetry (V.background theorem coarse small))
transformedSelectedBackgroundSatisfiesConstraint symmetry coarse small =
  constraintPreserved symmetry
    (V.backgroundSatisfiesConstraint _ coarse small)

transformedSelectedBackgroundInRegularGauge :
  ∀ {CoarseField FineField Bond Bound}
    {theorem : V.BackgroundFieldVariationalTheorem
      CoarseField FineField Bond Bound}
    (symmetry : InvolutiveVariationalSymmetry theorem)
    coarse
    (small : V.CoarseSmallField theorem coarse) →
  V.FineRegularGauge theorem
    (actFine symmetry (V.background theorem coarse small))
transformedSelectedBackgroundInRegularGauge symmetry coarse small =
  regularGaugePreserved symmetry
    (V.backgroundInRegularGauge _ coarse small)

backgroundNaturalityFromVariationalUniqueness :
  ∀ {CoarseField FineField Bond Bound}
    {theorem : V.BackgroundFieldVariationalTheorem
      CoarseField FineField Bond Bound}
    (symmetry : InvolutiveVariationalSymmetry theorem)
    (coarse : CoarseField)
    (small : V.CoarseSmallField theorem coarse) →
  let transformedSmall = smallPreserved symmetry coarse small
  in
  actFine symmetry (V.background theorem coarse small)
  ≡
  V.background theorem (actCoarse symmetry coarse) transformedSmall
backgroundNaturalityFromVariationalUniqueness
    {theorem = theorem} symmetry coarse small =
  let
    transformedCoarse = actCoarse symmetry coarse
    transformedSmall = smallPreserved symmetry coarse small

    oldBackground = V.background theorem coarse small
    transformedOld = actFine symmetry oldBackground
    newBackground = V.background theorem transformedCoarse transformedSmall

    transformedOldConstraint :
      V.FineConstraint theorem transformedCoarse transformedOld
    transformedOldConstraint =
      constraintPreserved symmetry
        (V.backgroundSatisfiesConstraint theorem coarse small)

    transformedOldGauge : V.FineRegularGauge theorem transformedOld
    transformedOldGauge =
      regularGaugePreserved symmetry
        (V.backgroundInRegularGauge theorem coarse small)

    newBelowTransformedOld :
      V.LessEqual theorem
        (V.action theorem newBackground)
        (V.action theorem transformedOld)
    newBelowTransformedOld =
      V.backgroundMinimizesAction theorem
        transformedCoarse transformedSmall transformedOld
        transformedOldConstraint transformedOldGauge

    twiceTransformedNewConstraintRaw :
      V.FineConstraint theorem
        (actCoarse symmetry transformedCoarse)
        (actFine symmetry newBackground)
    twiceTransformedNewConstraintRaw =
      constraintPreserved symmetry
        (V.backgroundSatisfiesConstraint theorem transformedCoarse transformedSmall)

    twiceTransformedNewConstraint :
      V.FineConstraint theorem coarse (actFine symmetry newBackground)
    twiceTransformedNewConstraint =
      subst
        (λ selectedCoarse →
          V.FineConstraint theorem selectedCoarse (actFine symmetry newBackground))
        (actCoarseInvolutive symmetry coarse)
        twiceTransformedNewConstraintRaw

    twiceTransformedNewGauge :
      V.FineRegularGauge theorem (actFine symmetry newBackground)
    twiceTransformedNewGauge =
      regularGaugePreserved symmetry
        (V.backgroundInRegularGauge theorem transformedCoarse transformedSmall)

    oldBelowTransformedNew :
      V.LessEqual theorem
        (V.action theorem oldBackground)
        (V.action theorem (actFine symmetry newBackground))
    oldBelowTransformedNew =
      V.backgroundMinimizesAction theorem
        coarse small (actFine symmetry newBackground)
        twiceTransformedNewConstraint twiceTransformedNewGauge

    oldBelowNew :
      V.LessEqual theorem
        (V.action theorem oldBackground)
        (V.action theorem newBackground)
    oldBelowNew =
      subst
        (λ right →
          V.LessEqual theorem (V.action theorem oldBackground) right)
        (actionInvariant symmetry newBackground)
        oldBelowTransformedNew

    transformedOldBelowNew :
      V.LessEqual theorem
        (V.action theorem transformedOld)
        (V.action theorem newBackground)
    transformedOldBelowNew =
      subst
        (λ left →
          V.LessEqual theorem left (V.action theorem newBackground))
        (sym (actionInvariant symmetry oldBackground))
        oldBelowNew

    equalActions :
      V.action theorem newBackground ≡ V.action theorem transformedOld
    equalActions =
      orderAntisymmetric symmetry
        newBelowTransformedOld transformedOldBelowNew
  in
  V.backgroundUnique theorem
    transformedCoarse transformedSmall transformedOld
    transformedOldConstraint transformedOldGauge
    (sym equalActions)

backgroundNaturalityFollowsFromInvariantVariationalProblem : Bool
backgroundNaturalityFollowsFromInvariantVariationalProblem = true

primitiveSelectedBackgroundEquivarianceRequired : Bool
primitiveSelectedBackgroundEquivarianceRequired = false
