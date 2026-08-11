module DASHI.Moonshine.Monster3BMultiplicityTwelveSeventyEightRecognitionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Make precise what must replace the numeral identity 90 = 12 + 78.  A valid
-- promotion supplies an actual two-sided decomposition of the multiplicity
-- carrier and proves that the inertia action is block diagonal under it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

ninetyIsTwelvePlusSeventyEight : 90 ≡ 12 + 78
ninetyIsTwelvePlusSeventyEight = refl

record TwelveSeventyEightRecognition
    (Multiplicity Inertia TwelveCarrier SeventyEightCarrier : Set) : Set₁ where
  field
    toSum : Multiplicity → TwelveCarrier ⊎ SeventyEightCarrier
    fromSum : TwelveCarrier ⊎ SeventyEightCarrier → Multiplicity
    fromAfterTo : (state : Multiplicity) → fromSum (toSum state) ≡ state
    toAfterFrom :
      (state : TwelveCarrier ⊎ SeventyEightCarrier) →
      toSum (fromSum state) ≡ state

    multiplicityAct : Inertia → Multiplicity → Multiplicity
    twelveAct : Inertia → TwelveCarrier → TwelveCarrier
    seventyEightAct : Inertia → SeventyEightCarrier → SeventyEightCarrier

    twelveIntertwines :
      (inertia : Inertia) →
      (state : TwelveCarrier) →
      toSum (multiplicityAct inertia (fromSum (inj₁ state)))
      ≡ inj₁ (twelveAct inertia state)

    seventyEightIntertwines :
      (inertia : Inertia) →
      (state : SeventyEightCarrier) →
      toSum (multiplicityAct inertia (fromSum (inj₂ state)))
      ≡ inj₂ (seventyEightAct inertia state)

open TwelveSeventyEightRecognition public

twelveBlockStable :
  ∀ {M I T S} →
  (recognition : TwelveSeventyEightRecognition M I T S) →
  (inertia : I) →
  (state : T) →
  toSum recognition
    (multiplicityAct recognition inertia
      (fromSum recognition (inj₁ state)))
  ≡ inj₁ (twelveAct recognition inertia state)
twelveBlockStable = twelveIntertwines

seventyEightBlockStable :
  ∀ {M I T S} →
  (recognition : TwelveSeventyEightRecognition M I T S) →
  (inertia : I) →
  (state : S) →
  toSum recognition
    (multiplicityAct recognition inertia
      (fromSum recognition (inj₂ state)))
  ≡ inj₂ (seventyEightAct recognition inertia state)
seventyEightBlockStable = seventyEightIntertwines

record TwelveSeventyEightPromotionBoundary : Set where
  constructor twelve-seventy-eight-promotion-boundary
  field
    dimensionCompatibility : 90 ≡ 12 + 78
    actualTwoSidedDecompositionConstructed : Bool
    actualTwoSidedDecompositionConstructedIsFalse :
      actualTwoSidedDecompositionConstructed ≡ false
    actualBlockIntertwiningConstructed : Bool
    actualBlockIntertwiningConstructedIsFalse :
      actualBlockIntertwiningConstructed ≡ false
    characterInnerProductsComputed : Bool
    characterInnerProductsComputedIsFalse :
      characterInnerProductsComputed ≡ false

canonicalTwelveSeventyEightPromotionBoundary :
  TwelveSeventyEightPromotionBoundary
canonicalTwelveSeventyEightPromotionBoundary =
  twelve-seventy-eight-promotion-boundary
    ninetyIsTwelvePlusSeventyEight
    false refl false refl false refl
