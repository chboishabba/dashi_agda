module DASHI.Analysis.FastCauchyOrder where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (_≤_)

open import DASHI.Analysis.FastCauchyReals

------------------------------------------------------------------------
-- Constructive order cannot be decided from one approximation.  Strict order
-- carries one persistent positive gap; non-strict order permits every requested
-- dyadic tolerance after a common cutoff.

record StrictFastCauchyWitness
  {A : RationalMetricAuthority}
  (x y : FastCauchyReal A) : Set₁ where
  field
    precision : Nat
    cutoff : Nat
    separated : ∀ m n →
      cutoff ≤ m →
      cutoff ≤ n →
      _≤Q_ A
        (_+Q_ A (approximate x m) (dyadicError A precision))
        (approximate y n)

open StrictFastCauchyWitness public

_<R_ :
  ∀ {A : RationalMetricAuthority} →
  FastCauchyReal A → FastCauchyReal A → Set
x <R y = StrictFastCauchyWitness x y

_≤R_ :
  ∀ {A : RationalMetricAuthority} →
  FastCauchyReal A → FastCauchyReal A → Set
_≤R_ {A} x y =
  ∀ precision →
  Σ Nat
    (λ cutoff →
      ∀ m n →
      cutoff ≤ m →
      cutoff ≤ n →
      _≤Q_ A
        (approximate x m)
        (_+Q_ A (approximate y n) (dyadicError A precision)))

record FastCauchyOrderLaws
  (A : RationalMetricAuthority) : Set₁ where
  field
    lessIrreflexive : ∀ x → x <R x → Set
    lessTransitive : ∀ {x y z} → x <R y → y <R z → x <R z
    lessRespectsEquality : ∀ {x x′ y y′} →
      x ≈R x′ → y ≈R y′ → x <R y → x′ <R y′

    lessEqualReflexive : ∀ x → x ≤R x
    lessEqualTransitive : ∀ {x y z} → x ≤R y → y ≤R z → x ≤R z
    lessEqualRespectsEquality : ∀ {x x′ y y′} →
      x ≈R x′ → y ≈R y′ → x ≤R y → x′ ≤R y′

    strictImpliesNonStrict : ∀ {x y} → x <R y → x ≤R y

open FastCauchyOrderLaws public

record ArchimedeanFastCauchyOrder
  (A : RationalMetricAuthority) : Set₁ where
  field
    embedNatural : Nat → FastCauchyReal A
    eventuallyAbove : ∀ x → Σ Nat (λ n → x <R embedNatural n)
    dyadicEventuallyBelowGap : ∀ {x y} → x <R y → Σ Nat (λ n → Set)

open ArchimedeanFastCauchyOrder public
