module DASHI.Physics.Closure.NSTriadKNHHBadTelescopingForcingRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Generated/leaked forcing can be easier to control as a conservative shell
-- transfer than by proving an arbitrary decay law.  If a nonnegative physical
-- potential F_q satisfies
--
--   beta_q <= F_q - F_(q+1),
--
-- then every forcing prefix telescopes:
--
--   sum_{q<n} beta_q <= F_0 - F_n <= F_0.
--
-- Hence Round 50's raw summable-forcing route closes with the exact budget
-- B_force = F_0.  The physical PDE search can therefore target a potential
-- drop for generated+leakage transfer before attempting pointwise beta decay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNHHBadSummableForcingRound50Exact as Sum

record TelescopingForcingPotential
    (input : Sum.BorderlineSummableForcing) : Set where
  field
    potential : Nat → ℚ
    potentialNonnegative : ∀ q → 0ℚ ≤ potential q
    forcingBelowPotentialDrop : ∀ q →
      Sum.forcing input q ≤ potential q - potential (suc q)

open TelescopingForcingPotential public

prefixBelowPotentialDrop :
  (input : Sum.BorderlineSummableForcing) →
  (telescoping : TelescopingForcingPotential input) →
  ∀ n →
  Sum.forcingPrefix input n
  ≤ potential telescoping zero - potential telescoping n
prefixBelowPotentialDrop input telescoping zero =
  subst
    (0ℚ ≤_)
    (solve (potential telescoping zero ∷ []))
    ℚP.≤-refl
prefixBelowPotentialDrop input telescoping (suc n) =
  let
    inherited :
      Sum.forcingPrefix input n + Sum.forcing input n
      ≤ (potential telescoping zero - potential telescoping n)
        + (potential telescoping n - potential telescoping (suc n))
    inherited =
      ℚP.+-mono-≤
        (prefixBelowPotentialDrop input telescoping n)
        (forcingBelowPotentialDrop telescoping n)
  in
  subst
    (Sum.forcingPrefix input (suc n) ≤_)
    (solve
      ( potential telescoping zero
      ∷ potential telescoping n
      ∷ potential telescoping (suc n)
      ∷ []))
    inherited

prefixBelowInitialPotential :
  (input : Sum.BorderlineSummableForcing) →
  (telescoping : TelescopingForcingPotential input) →
  ∀ n →
  Sum.forcingPrefix input n ≤ potential telescoping zero
prefixBelowInitialPotential input telescoping n =
  let
    dropBelowInitial :
      potential telescoping zero - potential telescoping n
      ≤ potential telescoping zero
    dropBelowInitial =
      ℚP.+-monoʳ-≤
        (potential telescoping zero)
        (ℚP.neg-mono-≤ (potentialNonnegative telescoping n))
  in
  ℚP.≤-trans
    (prefixBelowPotentialDrop input telescoping n)
    dropBelowInitial

telescopingPotentialToPrefixSummable :
  (input : Sum.BorderlineSummableForcing) →
  (telescoping : TelescopingForcingPotential input) →
  Sum.totalForcingBudget input ≡ potential telescoping zero →
  Sum.PrefixSummable input
telescopingPotentialToPrefixSummable input telescoping budgetExact = record
  { everyPrefixBelowBudget = λ n →
      subst
        (Sum.forcingPrefix input n ≤_)
        (sym budgetExact)
        (prefixBelowInitialPotential input telescoping n)
  }
  where
  open import Relation.Binary.PropositionalEquality using (sym)

telescopingGeneratedLeakageClosesRawForcingRoute : Bool
telescopingGeneratedLeakageClosesRawForcingRoute = true

telescopingGeneratedLeakageClosesRawForcingRouteIsTrue :
  telescopingGeneratedLeakageClosesRawForcingRoute ≡ true
telescopingGeneratedLeakageClosesRawForcingRouteIsTrue = refl
