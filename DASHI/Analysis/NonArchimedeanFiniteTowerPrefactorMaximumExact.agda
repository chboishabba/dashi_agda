module DASHI.Analysis.NonArchimedeanFiniteTowerPrefactorMaximumExact where

------------------------------------------------------------------------
-- FINITE TOWER PREFACTOR MAXIMUM
--
-- A finite dyadic detail tower has finitely many mean-zero shell components.
-- Each shell carries its own finite squared power prefactor.  The whole-level
-- prefactor can therefore be chosen as the finite maximum of those component
-- prefactors; no closed-form monotonicity formula is required for existence.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_≤_)

import DASHI.Core.FiniteWitnessMaximumExact as Maximum

record FiniteTowerShellAtlas : Set₁ where
  field
    Shell : Set
    shells : List Shell
    exhaustive : (shell : Shell) → shell ∈ shells
    squaredPrefactor : Shell → Nat

open FiniteTowerShellAtlas public

maximumSquaredPrefactor : FiniteTowerShellAtlas → Nat
maximumSquaredPrefactor atlas =
  Maximum.maxBy (squaredPrefactor atlas) (shells atlas)

shellPrefactorBelowMaximum :
  (atlas : FiniteTowerShellAtlas) →
  (shell : Shell atlas) →
  squaredPrefactor atlas shell ≤ maximumSquaredPrefactor atlas
shellPrefactorBelowMaximum atlas shell =
  Maximum.memberCostLeMaxBy
    (squaredPrefactor atlas)
    (exhaustive atlas shell)

record FiniteTowerPrefactorReceipt
    (atlas : FiniteTowerShellAtlas) : Set where
  field
    wholeSquaredPrefactor : Nat
    dominatesEveryShell :
      (shell : Shell atlas) →
      squaredPrefactor atlas shell ≤ wholeSquaredPrefactor

open FiniteTowerPrefactorReceipt public

compileFiniteTowerPrefactor :
  (atlas : FiniteTowerShellAtlas) →
  FiniteTowerPrefactorReceipt atlas
compileFiniteTowerPrefactor atlas = record
  { wholeSquaredPrefactor = maximumSquaredPrefactor atlas
  ; dominatesEveryShell = shellPrefactorBelowMaximum atlas
  }

------------------------------------------------------------------------
-- This compiler proves existence of a finite whole-level prefactor.  It does
-- not claim that the earlier explicit formula 2^(2^(n-2)-1) is the optimum or
-- even the selected maximum; proving a closed form is an optional refinement.
------------------------------------------------------------------------
