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
open import Data.Nat.Base using (_≤_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

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


------------------------------------------------------------------------
-- Exact finite threshold algebra. Unlike the truncated subtraction
-- n-k used by some executable encodings, the conjunction
-- `coverCount+k <= n` is well-typed for *all* k, including k>n, and is
-- equivalent to k<=cliqueCount. The later target adapter maps this
-- additive witness to the classical budget n-k with explicit k>n guard.
------------------------------------------------------------------------

cliqueBoundToCoverBound :
  (choices : List Bool) (k : Nat) →
  k ≤ countChosen choices →
  countChosen (flipChoices choices) + k ≤ length choices
cliqueBoundToCoverBound choices k lower =
  NatP.≤-trans
    (NatP.≤-reflexive
      (NatP.+-comm (countChosen (flipChoices choices)) k))
    (NatP.≤-trans
      (NatP.+-monoʳ-≤
        (countChosen (flipChoices choices)) lower)
      (NatP.≤-reflexive
        (trans
          (NatP.+-comm
            (countChosen (flipChoices choices))
            (countChosen choices))
          (cliqueCoverFiniteCardinalityComplement choices))))

coverBoundToCliqueBound :
  (choices : List Bool) (k : Nat) →
  countChosen (flipChoices choices) + k ≤ length choices →
  k ≤ countChosen choices
coverBoundToCliqueBound choices k upper =
  NatP.+-cancelʳ-≤
    k
    (countChosen choices)
    (countChosen (flipChoices choices))
    (subst
      (λ lower →
        lower ≤
          countChosen choices + countChosen (flipChoices choices))
      (NatP.+-comm
        (countChosen (flipChoices choices)) k)
      (subst
        (λ newUpper →
          countChosen (flipChoices choices) + k ≤ newUpper)
        (sym (cliqueCoverFiniteCardinalityComplement choices))
        upper))

karpCliqueCoverFiniteThresholdIff :
  (choices : List Bool) (k : Nat) →
  PR.Iff
    (k ≤ countChosen choices)
    (countChosen (flipChoices choices) + k ≤ length choices)
karpCliqueCoverFiniteThresholdIff choices k =
  PR.iff
    (cliqueBoundToCoverBound choices k)
    (coverBoundToCliqueBound choices k)
