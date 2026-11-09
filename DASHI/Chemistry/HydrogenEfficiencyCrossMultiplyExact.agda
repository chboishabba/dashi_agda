module DASHI.Chemistry.HydrogenEfficiencyCrossMultiplyExact where

-- Existing arithmetic proof machinery: Agda Data.Nat.Solver, as used in
-- DASHI.Algebra.BalancedTernaryRankNegationExact. Mathematical structure is
-- conventional engine efficiency = useful work / chemical input.
-- User-directed ChatGPT draft (2026-11-09). It proves symbolic algebra only;
-- no empirical McLaren/XFuel engine performance is assumed or certified.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

-- Nat ratios num/den represent rational efficiencies. Denominators are
-- strictly positive, so no zero-division witness can enter the model.
record MatchedOutputRatio : Set where
  field
    baselineDiesel : Nat
    assistedDiesel : Nat
    injectedHydrogenEnergy : Nat
    syntheticFuelEnergy : Nat
    usefulWork : Nat

    baselineNumerator : Nat
    baselineDenominator : Nat
    assistedNumerator : Nat
    assistedDenominator : Nat

    baselineDenominatorPositive : 0 < baselineDenominator
    assistedDenominatorPositive : 0 < assistedDenominator

    baselineWork :
      baselineNumerator * baselineDiesel
        ≡ usefulWork * baselineDenominator

    assistedWork :
      assistedNumerator *
        (assistedDiesel + injectedHydrogenEnergy + syntheticFuelEnergy)
        ≡ usefulWork * assistedDenominator

open MatchedOutputRatio public

-- Multiplication commutativity and associativity, supplied by the same
-- normalized Nat-polynomial solver already in DASHI.
exchangeFactors :
  (w a b : Nat) → (w * a) * b ≡ (w * b) * a
exchangeFactors w a b =
  solve 3
    (λ w a b → ((w :* a) :* b) := ((w :* b) :* a))
    refl w a b

-- A denominator-safe, exact cross-multiplication of two independently
-- supplied useful-work equations. The resulting relation is the
-- general efficiency constraint at identical useful output.
matchedOutputCrossMultiplies :
  (s : MatchedOutputRatio) →
  (baselineNumerator s * baselineDiesel s) * assistedDenominator s
  ≡
  (assistedNumerator s *
    (assistedDiesel s + injectedHydrogenEnergy s
      + syntheticFuelEnergy s)) * baselineDenominator s
matchedOutputCrossMultiplies s =
  trans
    (cong (λ x → x * assistedDenominator s) (baselineWork s))
    (trans
      (exchangeFactors (usefulWork s)
        (baselineDenominator s) (assistedDenominator s))
      (sym (cong (λ x → x * baselineDenominator s)
        (assistedWork s))))

-- Algebra does not establish that any observed H2 injection increases
-- useful-work efficiency; numerator and denominator identities require
-- measured, same-run calibration as separate external source obligations.
