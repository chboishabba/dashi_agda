module DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalDissipationTailClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Mathematical ingredient: absolute continuity of the Lebesgue integral for
-- an L1 time density.  The finite theorem below is repository-original and
-- has no DOI.
--
-- PURPOSE
-- Separate scale criticality from terminal smallness.  The commutator audit
-- reduces the newest-layer factor 2 lambda_q to the critical constant 2.
-- Therefore a normalized terminal dissipation tail of at most 1/128 closes
-- the 1/64 half-budget:
--
--   2 * tailMass <= 1/64.
--
-- The module also gives an explicit finite tail operator.  The continuum
-- producer must instantiate tailMass using the final parabolic interval and
-- prove its decay from integrability; no critical norm is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

record DissipationCell : Set where
  constructor dissipation-cell
  field
    mass : ℚ
    massNonnegative : 0ℚ ≤ mass

open DissipationCell public

sumDissipation : List DissipationCell → ℚ
sumDissipation [] = 0ℚ
sumDissipation (cell ∷ cells) =
  mass cell + sumDissipation cells

tailAfter : Nat → List DissipationCell → ℚ
tailAfter zero cells = sumDissipation cells
tailAfter (suc index) [] = 0ℚ
tailAfter (suc index) (cell ∷ cells) = tailAfter index cells

tailAfterSuccessor :
  (index : Nat) →
  (cell : DissipationCell) →
  (cells : List DissipationCell) →
  tailAfter (suc index) (cell ∷ cells)
  ≡ tailAfter index cells
tailAfterSuccessor index cell cells = refl

tailAfterEmpty :
  (index : Nat) →
  tailAfter index [] ≡ 0ℚ
tailAfterEmpty zero = refl
tailAfterEmpty (suc index) = refl

oneHundredTwentyEighth : ℚ
oneHundredTwentyEighth = Int.+ 1 / 128

oneSixtyFourth : ℚ
oneSixtyFourth = Int.+ 1 / 64

two : ℚ
two = Int.+ 2 / 1

record TerminalDissipationSmallness : Set where
  constructor terminal-dissipation-smallness
  field
    tailMass : ℚ
    tailNonnegative : 0ℚ ≤ tailMass
    tailBelowOneOver128 : tailMass ≤ oneHundredTwentyEighth

open TerminalDissipationSmallness public

criticalizedNearContribution : TerminalDissipationSmallness → ℚ
criticalizedNearContribution terminalData =
  two * tailMass terminalData

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

terminalDissipationClosesNearHalfBudget :
  (terminalData : TerminalDissipationSmallness) →
  criticalizedNearContribution terminalData
  ≤ oneSixtyFourth
terminalDissipationClosesNearHalfBudget terminalData =
  let
    instance
      twoIsNonnegative = nonNegative twoNonnegative

    scaled :
      two * tailMass terminalData
      ≤ two * oneHundredTwentyEighth
    scaled =
      ℚₚ.*-monoˡ-≤-nonNeg
        two
        (tailBelowOneOver128 terminalData)

    targetMeaning :
      two * oneHundredTwentyEighth ≡ oneSixtyFourth
    targetMeaning = solve []
  in
  subst
    (λ upper → criticalizedNearContribution terminalData ≤ upper)
    targetMeaning
    scaled
