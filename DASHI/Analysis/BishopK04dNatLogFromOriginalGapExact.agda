{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact where

------------------------------------------------------------------------
-- K04d-LOG: SOURCE NEGATIVE-LOG GAP -> EVERY NATIVE NAT EXP INVERSE.
--
-- Original source: Nat log candidate L_(n+2) from
--   BishopRiemannDirichletExponentialTermExact.sourceCanonicalNatLogCandidate.
-- It is NOT an arbitrary real-log function.
--
-- Reuse the exact existing non-postulatory Bishop exponential
-- cancellation and inverse-uniqueness compiler:
--   BishopNegativeLogExponentialReciprocalFromCancellationExact.
--
-- The *only* remaining ANALYTIC input is the original identity
--   exp_B(-L(x)) ~= 1-x  for the original convergent Bishop log series.
--
-- At the literal Nat ratio x=(n+1)/(n+2), the finite rational identity
-- (n+1)/(n+2)+1/(n+2)=1 gives 1-x=1/(n+2).
-- Native inverse uniqueness therefore gives exp_B(L(x))=n+2.
-- The Nat-zero log index is owned by the original Exp(0)=1 proof.
--
-- No selected classical log, independent Nat-index axiom, second
-- real carrier, or denominator division of an unproved nonzero term.
-- --safe source-written; exact Agda-2.9 acceptance still required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (refl)
open import Data.Integer.Base using (+_)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤSolver)
open ℤSolver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Rational.Unnormalised as Q using
  (ℚᵘ; 1ℚᵘ; _/_; _+_; _*_; _≃_; *≡*)

import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopNegativeLogExponentialReciprocalFromCancellationExact as Reciprocal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopInverseSquareProductExact as Inverse
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Gap

nativeNatRatio : Nat → ℚᵘ
nativeNatRatio n = + suc n / suc (suc n)

nativeNatReciprocal : Nat → ℚᵘ
nativeNatReciprocal n = + 1 / suc (suc n)

nativeNatSuccessor : Nat → ℚᵘ
nativeNatSuccessor n = + suc (suc n) / 1

-- One universal rational cross-multiplication proof, not a finite
-- regression or imported mathematical log theorem.
natRatioPlusReciprocalIsOne :
  (n : Nat) →
  Q._≃_
    (Q._+_ (nativeNatRatio n) (nativeNatReciprocal n))
    Q.1ℚᵘ
natRatioPlusReciprocalIsOne n =
  Q.*≡*
    (solve 1
      (λ k →
        ((((k :+ con (+ 1)) :* (k :+ con (+ 2)))
          :+ (con (+ 1) :* (k :+ con (+ 2))))
          :* con (+ 1))
        :=
        (con (+ 1) :*
          ((k :+ con (+ 2)) :* (k :+ con (+ 2)))))
      refl (+ n))

natReciprocalTimesSuccessorIsOne :
  (n : Nat) →
  Q._≃_
    (Q._*_ (nativeNatReciprocal n) (nativeNatSuccessor n))
    Q.1ℚᵘ
natReciprocalTimesSuccessorIsOne n =
  Q.*≡*
    (solve 1
      (λ denominator →
        ((con (+ 1) :* denominator) :* con (+ 1))
          :=
        (con (+ 1) :* (denominator :* con (+ 1))))
      refl (+ suc (suc n)))

nativeNatArgumentPlusReciprocalIsOne :
  (n : Nat) →
  R._≃_
    (R._+_
      (Terms.natLogArgument n)
      (R._⋆ (nativeNatReciprocal n)))
    R.1ℝ
nativeNatArgumentPlusReciprocalIsOne n =
  RP.≃-trans
    (RP.≃-symm
      (RP.⋆-distrib-+
        (nativeNatRatio n) (nativeNatReciprocal n)))
    (RP.⋆-cong (natRatioPlusReciprocalIsOne n))

nativeNatGapIsReciprocal :
  (n : Nat) →
  R._≃_
    (Identity.oneMinus (Terms.natLogArgument n))
    (R._⋆ (nativeNatReciprocal n))
nativeNatGapIsReciprocal n =
  let
    ratio = Terms.natLogArgument n
    reciprocal = R._⋆ (nativeNatReciprocal n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (RP.≃-symm
        (nativeNatArgumentPlusReciprocalIsOne n))
      RP.≃-refl)
    (solve 2
      (λ x y →
        (x ⊕ y) ⊖ x ⊜ y)
      RP.≃-refl ratio reciprocal)

nativeNatReciprocalTimesValueIsOne :
  (n : Nat) →
  R._≃_
    (R._*_
      (R._⋆ (nativeNatReciprocal n))
      (NatReal.natReal (suc (suc n))))
    R.1ℝ
nativeNatReciprocalTimesValueIsOne n =
  RP.≃-trans
    (RP.≃-symm
      (RP.⋆-distrib-*
        (nativeNatReciprocal n) (nativeNatSuccessor n)))
    (RP.⋆-cong (natReciprocalTimesSuccessorIsOne n))

nativeNatGapTimesSuccessorIsOne :
  (n : Nat) →
  R._≃_
    (R._*_
      (Identity.oneMinus (Terms.natLogArgument n))
      (NatReal.natReal (suc (suc n))))
    R.1ℝ
nativeNatGapTimesSuccessorIsOne n =
  RP.≃-trans
    (RP.*-cong (nativeNatGapIsReciprocal n) RP.≃-refl)
    (nativeNatReciprocalTimesValueIsOne n)

-- Unlike an arbitrary theorem parameter, this type asserts one
-- source-specified global analytic equality for the LITERAL
-- convergent native Bishop negative-log series.
OriginalBishopNegativeLogExponentialGap : Set
OriginalBishopNegativeLogExponentialGap =
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R._≃_
    (Exp.bishopExp
      (R.-_ (Log.sourceNegativeLogValue x positive belowOne)))
    (Identity.oneMinus x)

sourceCanonicalNatLogSuccessorExpInverse :
  OriginalBishopNegativeLogExponentialGap →
  (n : Nat) →
  R._≃_
    (Exp.bishopExp (Terms.sourceCanonicalNatLogCandidate (suc n)))
    (NatReal.natReal (suc (suc n)))
sourceCanonicalNatLogSuccessorExpInverse gapLaw n =
  let
    x = Terms.natLogArgument n
    positive = Terms.natLogArgumentPositiveBishop n
    belowOne = Terms.natLogArgumentBelowOneBishop n
    nonzero =
      Gap.gapNonzero (Reciprocal.sourceOneMinusRatio x positive belowOne)
    inverseForOriginalLog =
      Reciprocal.negativeLogExpIsActualBishopInverse
        x positive belowOne (gapLaw x positive belowOne)
    inverseForNatSuccessor =
      Inverse.inverseFromCancellation
        (Identity.oneMinus x)
        (NatReal.natReal (suc (suc n)))
        nonzero
        (RP.≃-trans
          (RP.*-comm
            (NatReal.natReal (suc (suc n)))
            (Identity.oneMinus x))
          (nativeNatGapTimesSuccessorIsOne n))
  in
  RP.≃-trans inverseForOriginalLog inverseForNatSuccessor

sourceCanonicalNatLogAllIndicesExpInverse :
  OriginalBishopNegativeLogExponentialGap →
  (n : Nat) →
  R._≃_
    (Exp.bishopExp (Terms.sourceCanonicalNatLogCandidate n))
    (NatReal.natReal (suc n))
sourceCanonicalNatLogAllIndicesExpInverse gapLaw zero =
  Terms.sourceCanonicalOriginalExpLogInverseAtOne
sourceCanonicalNatLogAllIndicesExpInverse gapLaw (suc n) =
  sourceCanonicalNatLogSuccessorExpInverse gapLaw n
