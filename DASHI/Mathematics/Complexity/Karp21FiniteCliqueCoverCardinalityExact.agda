module DASHI.Mathematics.Complexity.Karp21FiniteCliqueCoverCardinalityExact where

------------------------------------------------------------------------
-- Karp (1972) CLIQUE -> NODE COVER cardinality bridge.
-- Every finite picked vertex list and its pointwise complement partition
-- the vertex positions, so |picked| + |complement| = number of vertices.
-- Duplicate graph labels cannot collapse distinct vertex *positions*.
--
-- DASHI reuses exact Boolean complement semantics in
-- Karp21CliqueVertexCoverExact and the standard Nat +-suc law.
-- A later graph instance owner must couple this sum equality to
-- CLIQUE's >=k and NODE COVER's <=n-k cut, for all k>n / malformed words.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

countChosen : List Bool → Nat
countChosen [] = zero
countChosen (true ∷ xs) = suc (countChosen xs)
countChosen (false ∷ xs) = countChosen xs

countNotChosen : List Bool → Nat
countNotChosen [] = zero
countNotChosen (true ∷ xs) = countNotChosen xs
countNotChosen (false ∷ xs) = suc (countNotChosen xs)

flipChoices : List Bool → List Bool
flipChoices [] = []
flipChoices (bit ∷ xs) =
  Graph.negBool bit ∷ flipChoices xs

chosenAndUnchosenAddToLength :
  (choices : List Bool) →
  countChosen choices + countNotChosen choices ≡ length choices
chosenAndUnchosenAddToLength [] = refl
chosenAndUnchosenAddToLength (true ∷ xs) =
  cong suc (chosenAndUnchosenAddToLength xs)
chosenAndUnchosenAddToLength (false ∷ xs) =
  trans
    (NatP.+-suc (countChosen xs) (countNotChosen xs))
    (cong suc (chosenAndUnchosenAddToLength xs))

countFlippedEqualsNotChosen :
  (choices : List Bool) →
  countChosen (flipChoices choices) ≡ countNotChosen choices
countFlippedEqualsNotChosen [] = refl
countFlippedEqualsNotChosen (true ∷ xs) =
  countFlippedEqualsNotChosen xs
countFlippedEqualsNotChosen (false ∷ xs) =
  cong suc (countFlippedEqualsNotChosen xs)

cliqueCoverFiniteCardinalityComplement :
  (choices : List Bool) →
  countChosen choices + countChosen (flipChoices choices) ≡
  length choices
cliqueCoverFiniteCardinalityComplement choices =
  trans
    (cong (λ unchosen → countChosen choices + unchosen)
      (countFlippedEqualsNotChosen choices))
    (chosenAndUnchosenAddToLength choices)
