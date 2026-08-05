module DASHI.Physics.Closure.NSTriadKNCherevanWideNarrowAssemblyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Source under audit:
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- PURPOSE
-- Correct the repeated assembly
--
--   R = R_wide + R_narrow  ==>  ||R|| <= min{A_wide,A_narrow}.
--
-- Separate upper bounds add; they do not combine by taking a minimum.  If
-- both pieces are bounded by a common dominant envelope B, the correct bound
-- is 2B (or A_wide+A_narrow).  The exponent conclusion may survive when the
-- faster term is dominated by the slower one, but the constant and logical
-- theorem must be assembled honestly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

record TwoRegionBudget : Set where
  constructor two-region-budget
  field
    wide narrow dominant : ℚ
    wideBound : wide ≤ dominant
    narrowBound : narrow ≤ dominant

open TwoRegionBudget public

totalRegionContribution : TwoRegionBudget → ℚ
totalRegionContribution budget = wide budget + narrow budget

twoTimesDominant : TwoRegionBudget → ℚ
twoTimesDominant budget = (Int.+ 2 / 1) * dominant budget

correctTwoRegionAssembly :
  (budget : TwoRegionBudget) →
  totalRegionContribution budget ≤ twoTimesDominant budget
correctTwoRegionAssembly budget =
  let
    summed :
      wide budget + narrow budget
      ≤ dominant budget + dominant budget
    summed = ℚₚ.+-mono-≤ (wideBound budget) (narrowBound budget)

    targetMeaning :
      dominant budget + dominant budget
      ≡ (Int.+ 2 / 1) * dominant budget
    targetMeaning = solve (dominant budget ∷ [])
  in
  subst
    (λ upper → totalRegionContribution budget ≤ upper)
    targetMeaning
    summed

wideWitness narrowWitness selectedMinimum totalWitness : ℚ
wideWitness = Int.+ 1 / 8
narrowWitness = Int.+ 1 / 2
selectedMinimum = wideWitness
totalWitness = wideWitness + narrowWitness

minimumAssemblyFailsOnWitness :
  selectedMinimum < totalWitness
minimumAssemblyFailsOnWitness =
  toWitness {a? = selectedMinimum ℚₚ.<? totalWitness} _

totalWitnessIsFiveEighths :
  totalWitness ≡ Int.+ 5 / 8
totalWitnessIsFiveEighths = solve []
