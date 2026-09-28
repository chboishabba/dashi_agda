{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRunningCouplingOrientationFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
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

naiveSameSuccessorForcesBetaZero :
  (dataSet : NaiveSameSuccessorIdentification) →
  beta dataSet ≡ 0ℚ
naiveSameSuccessorForcesBetaZero dataSet =
  let
    c = current dataSet
    n = next dataSet
    b = beta dataSet

    combined :
      c ≡ (c + b) + b
    combined =
      trans
        (cmp109SourceOrientation dataSet)
        (subst
          (λ selected → c ≡ selected + b)
          (sym (literalPlaquetteOrientation dataSet))
          refl)
  in
  ℚRing.solve c b combined

strictPositiveBetaBlocksNaiveSameSuccessor :
  (dataSet : NaiveSameSuccessorIdentification) →
  0ℚ < beta dataSet →
  ℚ.⊥
strictPositiveBetaBlocksNaiveSameSuccessor dataSet betaPositive =
  ℚP.<-irrefl
    (naiveSameSuccessorForcesBetaZero dataSet)
    betaPositive

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
