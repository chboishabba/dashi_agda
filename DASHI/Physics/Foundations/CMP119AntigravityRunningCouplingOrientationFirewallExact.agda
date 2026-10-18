{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRunningCouplingOrientationFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

------------------------------------------------------------------------
-- SAME-OBJECT RUNNING-COUPLING ORIENTATION FIREWALL
--
-- Literal plaquette producer convention:
--
--   next = current + beta_lit.
--
-- CMP109 source-successor convention:
--
--   current = next + beta_src.
--
-- If one identifies beta_lit = beta_src without reversing the scale direction
-- or changing sign, then beta must vanish.  Hence a strictly positive beta
-- makes the naive same-successor identification impossible.
------------------------------------------------------------------------

record NaiveSameSuccessorIdentification : Set where
  field
    current next beta : ℚ

    literalPlaquetteOrientation :
      next ≡ current + beta

    cmp109SourceOrientation :
      current ≡ next + beta

open NaiveSameSuccessorIdentification public

strictPositiveBetaBlocksNaiveSameSuccessor :
  (dataSet : NaiveSameSuccessorIdentification) →
  0ℚ < beta dataSet →
  ⊥
strictPositiveBetaBlocksNaiveSameSuccessor dataSet betaPositive =
  let
    c = current dataSet
    n = next dataSet
    b = beta dataSet

    zeroPlusCurrentIsCurrent : 0ℚ + c ≡ c
    zeroPlusCurrentIsCurrent = ℚRing.solve-∀ c

    betaPlusCurrentIsCurrentPlusBeta : b + c ≡ c + b
    betaPlusCurrentIsCurrentPlusBeta = ℚRing.solve-∀ c b

    currentBelowCurrentPlusBeta : c < c + b
    currentBelowCurrentPlusBeta =
      subst
        (λ left → left < c + b)
        zeroPlusCurrentIsCurrent
        (subst
          (λ right → 0ℚ + c < right)
          betaPlusCurrentIsCurrentPlusBeta
          (ℚP.+-monoʳ-< c betaPositive))

    currentBelowNext : c < n
    currentBelowNext =
      subst
        (c <_)
        (sym (literalPlaquetteOrientation dataSet))
        currentBelowCurrentPlusBeta

    zeroPlusNextIsNext : 0ℚ + n ≡ n
    zeroPlusNextIsNext = ℚRing.solve-∀ n

    betaPlusNextIsNextPlusBeta : b + n ≡ n + b
    betaPlusNextIsNextPlusBeta = ℚRing.solve-∀ n b

    nextBelowNextPlusBeta : n < n + b
    nextBelowNextPlusBeta =
      subst
        (λ left → left < n + b)
        zeroPlusNextIsNext
        (subst
          (λ right → 0ℚ + n < right)
          betaPlusNextIsNextPlusBeta
          (ℚP.+-monoʳ-< n betaPositive))

    nextBelowCurrent : n < c
    nextBelowCurrent =
      subst
        (n <_)
        (sym (cmp109SourceOrientation dataSet))
        nextBelowNextPlusBeta

    currentBelowCurrent : c < c
    currentBelowCurrent =
      ℚP.<-trans currentBelowNext nextBelowCurrent
  in
  (ℚP.<-irrefl refl) currentBelowCurrent

naiveSameSuccessorIdentificationAllowed : Bool
naiveSameSuccessorIdentificationAllowed = false

scaleReversalOrIncrementSignConversionRequired : Bool
scaleReversalOrIncrementSignConversionRequired = true

naiveSameSuccessorIdentificationAllowedIsFalse :
  naiveSameSuccessorIdentificationAllowed ≡ false
naiveSameSuccessorIdentificationAllowedIsFalse = refl

scaleReversalOrIncrementSignConversionRequiredIsTrue :
  scaleReversalOrIncrementSignConversionRequired ≡ true
scaleReversalOrIncrementSignConversionRequiredIsTrue = refl
