module DASHI.NumberTheory.ThreeAdicCompletionCutset where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.NumberTheory.ThreeAdicDigitAttractor as Digit

record ConcreteThreeAdicCompletion : Set₁ where
  field
    finitePrefixAuthority : Digit.ThreeAdicCompletionAuthority
    Point Rational : Set
    valuation : Rational → Nat
    metric : Point → Point → Nat
    rationalEmbedding : Rational → Point
    allOnesPrefixPoint : Nat → Point
    allOnesLimit : Point
    Cauchy : (Nat → Point) → Set
    LimitOf : (Nat → Point) → Point → Set
    allOnesPrefixesCauchy : Cauchy allOnesPrefixPoint
    completionSuppliesLimit : LimitOf allOnesPrefixPoint allOnesLimit
    minusHalf : Rational
    limitIsEmbeddedMinusHalf : allOnesLimit ≡ rationalEmbedding minusHalf
    metricIsThreeAdic : Set
    completionIsComplete : Set

open ConcreteThreeAdicCompletion public

record ThreeAdicCompletionCutsetBoundary : Set where
  constructor threeAdicCompletionCutsetBoundary
  field
    finitePrefixTheoremReused : Bool
    q3CarrierConstructedInThisCutset : Bool
    q3CarrierConstructedInThisCutsetIsFalse :
      q3CarrierConstructedInThisCutset ≡ false
    minusHalfClaimAvailableWithoutConcreteAuthority : Bool
    minusHalfClaimAvailableWithoutConcreteAuthorityIsFalse :
      minusHalfClaimAvailableWithoutConcreteAuthority ≡ false

canonicalThreeAdicCompletionCutsetBoundary : ThreeAdicCompletionCutsetBoundary
canonicalThreeAdicCompletionCutsetBoundary =
  threeAdicCompletionCutsetBoundary true false refl false refl
