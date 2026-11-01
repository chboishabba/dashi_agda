module DASHI.Analysis.MarxConstructiveRealNamedLemmas where

open import Agda.Primitive using (Set)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.MarxConstructiveRealRingNormalisation

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Stable theorem names for the completion ledger.  The proofs are direct
-- projections from ConstructedRealRingNormalisationLaws; no duplicate
-- authority is introduced.

constructedRealMulZeroRight :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  ∀ x → _*_ R x (zero R) ≡ zero R
constructedRealMulZeroRight = mulZeroRightLaw

constructedRealSubAsAddNeg :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  ∀ x y → _-_ R x y ≡ _+_ R x (neg R y)
constructedRealSubAsAddNeg = subAsAddNeg

constructedRealNegAdd :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  ∀ x y → neg R (_+_ R x y) ≡ _+_ R (neg R x) (neg R y)
constructedRealNegAdd = negAdd

constructedRealDifferenceOfSums :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  ∀ a a₁ b b₁ →
  _-_ R (_+_ R a₁ b₁) (_+_ R a b)
  ≡ _+_ R (_-_ R a₁ a) (_-_ R b₁ b)
constructedRealDifferenceOfSums = differenceOfSums

constructedRealDifferenceOfProducts :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  ∀ a a₁ b b₁ →
  _-_ R (_*_ R a₁ b₁) (_*_ R a b)
  ≡ _+_ R
      (_*_ R (_-_ R a₁ a) b₁)
      (_*_ R a (_-_ R b₁ b))
constructedRealDifferenceOfProducts = differenceOfProducts

constructedRealZeroNotOne :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  zero R ≢ one R
constructedRealZeroNotOne = zeroNotOne

constructedRealTwoNonzero :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ConstructedRealRingNormalisationLaws R →
  _+_ R (one R) (one R) ≢ zero R
constructedRealTwoNonzero = twoNonzero
