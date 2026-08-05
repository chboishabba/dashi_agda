module DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalFarNearBudgetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Close the exact scalar composition created by the terminal far/near split.
-- Separate physical estimates for the old history and the newest parabolic
-- layer imply the complete terminal estimate.  In particular,
--
--   far <= 1/64,  near <= 1/64
--     => far+near <= 1/32.
--
-- The theorem makes the remaining frontier precise: the near producer must
-- pay one half of the Luo smallness budget after the far history has been
-- damped into the other half.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; _/_; _+_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record TerminalFarNearBudget : Set where
  constructor terminal-far-near-budget
  field
    farValue nearValue farEnvelope nearEnvelope : ℚ
    farBound : farValue ≤ farEnvelope
    nearBound : nearValue ≤ nearEnvelope

open TerminalFarNearBudget public

totalTerminalValue : TerminalFarNearBudget → ℚ
totalTerminalValue budget = farValue budget + nearValue budget

totalTerminalEnvelope : TerminalFarNearBudget → ℚ
totalTerminalEnvelope budget = farEnvelope budget + nearEnvelope budget

farNearEnvelopeBound :
  (budget : TerminalFarNearBudget) →
  totalTerminalValue budget ≤ totalTerminalEnvelope budget
farNearEnvelopeBound budget =
  ℚₚ.+-mono-≤ (farBound budget) (nearBound budget)

oneSixtyFourth oneThirtySecond : ℚ
oneSixtyFourth = Int.+ 1 / 64
oneThirtySecond = Int.+ 1 / 32

twoHalfBudgetsMakeLuoSmallness :
  ∀ {farValue nearValue : ℚ} →
  farValue ≤ oneSixtyFourth →
  nearValue ≤ oneSixtyFourth →
  farValue + nearValue ≤ oneThirtySecond
twoHalfBudgetsMakeLuoSmallness {farValue} {nearValue} farSmall nearSmall =
  let
    combined :
      farValue + nearValue ≤ oneSixtyFourth + oneSixtyFourth
    combined = ℚₚ.+-mono-≤ farSmall nearSmall
  in
  subst
    (λ upper → farValue + nearValue ≤ upper)
    (solve [])
    combined
