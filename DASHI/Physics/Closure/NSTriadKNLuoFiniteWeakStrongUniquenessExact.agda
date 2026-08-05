module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeakStrongUniquenessExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Emil Wiedemann.
-- Title: "Weak-Strong Uniqueness in Fluid Dynamics".
-- In: Partial Differential Equations in Fluid Mechanics, Cambridge
-- University Press, 2019, pp. 289--326.
-- DOI: 10.1017/9781108610575.012.
-- arXiv DOI: 10.48550/arXiv.1705.04220.
--
-- PURPOSE
-- Prove the finite relative-energy core of weak--strong uniqueness rather
-- than select an unspecified weak branch.  If a nonnegative difference
-- energy starts at zero and obeys the homogeneous recurrence
--
--   E(n+1) <= (1+a(n)) E(n),
--
-- then every finite-time difference energy is exactly zero.  The continuum
-- relative-energy inequality and its identification with a particular
-- maximal strong solution remain separate analytic producers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record FiniteRelativeEnergyUniqueness : Set where
  constructor finite-relative-energy-uniqueness
  field
    differenceEnergy growth : Nat → ℚ

    energyNonnegative :
      (time : Nat) → 0ℚ ≤ differenceEnergy time

    initialAgreement : differenceEnergy zero ≡ 0ℚ

    homogeneousRelativeEnergyStep :
      (time : Nat) →
      differenceEnergy (suc time)
      ≤ (1ℚ + growth time) * differenceEnergy time

open FiniteRelativeEnergyUniqueness public

finiteWeakStrongAgreement :
  (inputs : FiniteRelativeEnergyUniqueness) →
  (time : Nat) →
  differenceEnergy inputs time ≡ 0ℚ
finiteWeakStrongAgreement inputs zero = initialAgreement inputs
finiteWeakStrongAgreement inputs (suc time) =
  let
    upperRaw = homogeneousRelativeEnergyStep inputs time

    upperZero : differenceEnergy inputs (suc time) ≤ 0ℚ
    upperZero =
      subst
        (λ upper → differenceEnergy inputs (suc time) ≤ upper)
        (solve (growth inputs time ∷ []))
        (subst
          (λ previous →
            differenceEnergy inputs (suc time)
            ≤ (1ℚ + growth inputs time) * previous)
          (finiteWeakStrongAgreement inputs time)
          upperRaw)
  in
  ℚₚ.≤-antisym
    upperZero
    (energyNonnegative inputs (suc time))
