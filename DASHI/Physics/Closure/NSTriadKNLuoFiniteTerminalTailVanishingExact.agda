module DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalTailVanishingExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Mathematical ingredient: absolute continuity of the Lebesgue integral for
-- L^1 densities.  The theorem below is the exact finite-list analogue and is
-- repository-original; no DOI is assigned.
--
-- PURPOSE
-- Complete the finite terminal-tail lane left open in round nine.  Every
-- finite nonnegative dissipation history has an exactly zero tail after its
-- final cell.  Therefore the round-nine 1/128 smallness record and 1/64
-- closure theorem can be instantiated at that finite endpoint.
--
-- This is not the continuum absolute-continuity theorem.  Countable time,
-- Lebesgue integration, and the q-dependent terminal interval remain separate
-- analytic producers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalDissipationTailClosureExact as Tail

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ values) = suc (length values)

tailAfterLengthVanishes :
  (cells : List Tail.DissipationCell) →
  Tail.tailAfter (length cells) cells ≡ 0ℚ
tailAfterLengthVanishes [] = refl
tailAfterLengthVanishes (cell ∷ cells) =
  tailAfterLengthVanishes cells

zeroNonnegative : 0ℚ ≤ 0ℚ
zeroNonnegative = toWitness {a? = 0ℚ ≤? 0ℚ} _

zeroBelowOneHundredTwentyEighth :
  0ℚ ≤ Tail.oneHundredTwentyEighth
zeroBelowOneHundredTwentyEighth =
  toWitness {a? = 0ℚ ≤? Tail.oneHundredTwentyEighth} _

terminalSmallnessAtFiniteEnd :
  (cells : List Tail.DissipationCell) →
  Tail.TerminalDissipationSmallness
terminalSmallnessAtFiniteEnd cells =
  Tail.terminal-dissipation-smallness
    (Tail.tailAfter (length cells) cells)
    (subst
      (λ tail → 0ℚ ≤ tail)
      (sym (tailAfterLengthVanishes cells))
      zeroNonnegative)
    (subst
      (λ tail → tail ≤ Tail.oneHundredTwentyEighth)
      (sym (tailAfterLengthVanishes cells))
      zeroBelowOneHundredTwentyEighth)

finiteEndpointClosesNearHalfBudget :
  (cells : List Tail.DissipationCell) →
  Tail.criticalizedNearContribution
    (terminalSmallnessAtFiniteEnd cells)
  ≤ Tail.oneSixtyFourth
finiteEndpointClosesNearHalfBudget cells =
  Tail.terminalDissipationClosesNearHalfBudget
    (terminalSmallnessAtFiniteEnd cells)
