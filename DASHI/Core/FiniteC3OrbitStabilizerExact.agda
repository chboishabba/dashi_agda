module DASHI.Core.FiniteC3OrbitStabilizerExact where

------------------------------------------------------------------------
-- FINITE ORBIT / STABILIZER CORE
--
-- Primary reference:
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163, Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- This module proves an explicit C3 action with two stabilizer strata: a
-- regular three-point orbit and one fixed point.  It is a finite exact model
-- of the general principle "enhanced stabilizer -> smaller orbit".  It does
-- not claim a Calabi--Yau theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_*_)
open import Relation.Binary.PropositionalEquality using (cong)

data C3 : Set where
  c0 c1 c2 : C3

_∙_ : C3 → C3 → C3
c0 ∙ x = x
c1 ∙ c0 = c1
c1 ∙ c1 = c2
c1 ∙ c2 = c0
c2 ∙ c0 = c2
c2 ∙ c1 = c0
c2 ∙ c2 = c1

inverse : C3 → C3
inverse c0 = c0
inverse c1 = c2
inverse c2 = c1

leftIdentity : ∀ x → c0 ∙ x ≡ x
leftIdentity x = refl

rightIdentity : ∀ x → x ∙ c0 ≡ x
rightIdentity c0 = refl
rightIdentity c1 = refl
rightIdentity c2 = refl

inverseLeft : ∀ x → inverse x ∙ x ≡ c0
inverseLeft c0 = refl
inverseLeft c1 = refl
inverseLeft c2 = refl

inverseRight : ∀ x → x ∙ inverse x ≡ c0
inverseRight c0 = refl
inverseRight c1 = refl
inverseRight c2 = refl

associative : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
associative c0 y z = refl
associative c1 c0 z = refl
associative c1 c1 c0 = refl
associative c1 c1 c1 = refl
associative c1 c1 c2 = refl
associative c1 c2 c0 = refl
associative c1 c2 c1 = refl
associative c1 c2 c2 = refl
associative c2 c0 z = refl
associative c2 c1 c0 = refl
associative c2 c1 c1 = refl
associative c2 c1 c2 = refl
associative c2 c2 c0 = refl
associative c2 c2 c1 = refl
associative c2 c2 c2 = refl

act : C3 → C3 → C3
act = _∙_

actIdentity : ∀ x → act c0 x ≡ x
actIdentity = leftIdentity

actComposition : ∀ g h x → act (g ∙ h) x ≡ act g (act h x)
actComposition g h x = associative g h x

length : ∀ {A} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

groupElements : List C3
groupElements = c0 ∷ c1 ∷ c2 ∷ []

groupSize : length groupElements ≡ 3
groupSize = refl

orbit : C3 → List C3
orbit c0 = c0 ∷ c1 ∷ c2 ∷ []
orbit c1 = c1 ∷ c2 ∷ c0 ∷ []
orbit c2 = c2 ∷ c0 ∷ c1 ∷ []

stabilizer : C3 → List C3
stabilizer c0 = c0 ∷ []
stabilizer c1 = c0 ∷ []
stabilizer c2 = c0 ∷ []

orbitSize : ∀ x → length (orbit x) ≡ 3
orbitSize c0 = refl
orbitSize c1 = refl
orbitSize c2 = refl

stabilizerSize : ∀ x → length (stabilizer x) ≡ 1
stabilizerSize c0 = refl
stabilizerSize c1 = refl
stabilizerSize c2 = refl

orbitStabilizerRegularCardinality : ∀ x →
  length groupElements ≡ length (orbit x) * length (stabilizer x)
orbitStabilizerRegularCardinality c0 = refl
orbitStabilizerRegularCardinality c1 = refl
orbitStabilizerRegularCardinality c2 = refl

data StratifiedPoint : Set where
  moving : C3 → StratifiedPoint
  fixed : StratifiedPoint

stratifiedAct : C3 → StratifiedPoint → StratifiedPoint
stratifiedAct g (moving x) = moving (g ∙ x)
stratifiedAct g fixed = fixed

stratifiedActIdentity : ∀ x → stratifiedAct c0 x ≡ x
stratifiedActIdentity (moving x) = refl
stratifiedActIdentity fixed = refl

stratifiedActComposition : ∀ g h x →
  stratifiedAct (g ∙ h) x ≡ stratifiedAct g (stratifiedAct h x)
stratifiedActComposition g h (moving x) = cong moving (associative g h x)
stratifiedActComposition g h fixed = refl

fixedOrbit : List StratifiedPoint
fixedOrbit = fixed ∷ []

fixedStabilizer : List C3
fixedStabilizer = c0 ∷ c1 ∷ c2 ∷ []

fixedOrbitSize : length fixedOrbit ≡ 1
fixedOrbitSize = refl

fixedStabilizerSize : length fixedStabilizer ≡ 3
fixedStabilizerSize = refl

orbitStabilizerFixedCardinality :
  length groupElements ≡ length fixedOrbit * length fixedStabilizer
orbitStabilizerFixedCardinality = refl

record SymmetryEnhancementReceipt : Set where
  constructor symmetryEnhancementReceipt
  field
    regularOrbitCardinality : Nat
    regularStabilizerCardinality : Nat
    enhancedOrbitCardinality : Nat
    enhancedStabilizerCardinality : Nat
    regularOrbitIsThree : regularOrbitCardinality ≡ 3
    regularStabilizerIsOne : regularStabilizerCardinality ≡ 1
    enhancedOrbitIsOne : enhancedOrbitCardinality ≡ 1
    enhancedStabilizerIsThree : enhancedStabilizerCardinality ≡ 3

open SymmetryEnhancementReceipt public

c3SymmetryEnhancementReceipt : SymmetryEnhancementReceipt
c3SymmetryEnhancementReceipt =
  symmetryEnhancementReceipt 3 1 1 3 refl refl refl refl

record OrbitReceipt : Set where
  constructor orbitReceipt
  field
    point : C3
    orbitCarrier : List C3
    stabilizerCarrier : List C3
    orbitCardinality : length orbitCarrier ≡ 3
    stabilizerCardinality : length stabilizerCarrier ≡ 1

open OrbitReceipt public

regularOrbitReceipt : C3 → OrbitReceipt
regularOrbitReceipt x = orbitReceipt x (orbit x) (stabilizer x) (orbitSize x) (stabilizerSize x)
