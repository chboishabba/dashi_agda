module DASHI.Core.FinitePrefactorEnergyAssemblyExact where

------------------------------------------------------------------------
-- FINITE PREFACTOR ENERGY ASSEMBLY
--
-- Generic finite compiler:
--
--   output(s) <= envelope(c_s,s)
--   c_s <= C
--   envelope monotone in the prefactor coordinate
--
-- for every shell s implies
--
--   sum_s output(s) <= sum_s envelope(C,s).
--
-- The ordered-additive structure is reused from MDLDescentTradeoff.  This is
-- exactly the whole-level step needed after selecting a finite maximum shell
-- prefactor.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

import DASHI.MDL.MDLDescentTradeoff as Ordered

open Ordered.AddMonoid
open Ordered.OrderedMonoid

sumBy :
  ∀ {ℓ s} →
  {Shell : Set s} →
  (O : Ordered.OrderedMonoid {ℓ}) →
  (Shell → N (M O)) →
  List Shell →
  N (M O)
sumBy O value [] = 0# (M O)
sumBy O value (shell ∷ shells) =
  Ordered.AddMonoid._+_ (M O)
    (value shell)
    (sumBy O value shells)

record PrefactorEnergyData {ℓ s} : Set (lsuc (ℓ ⊔ s)) where
  field
    Shell : Set s
    O : Ordered.OrderedMonoid {ℓ}
    shells : List Shell

    localPrefactor : Shell → Nat
    globalPrefactor : Nat
    localPrefactor≤global :
      (shell : Shell) → localPrefactor shell ≤ globalPrefactor

    outputEnergy : Shell → N (M O)
    envelope : Nat → Shell → N (M O)

    localBound :
      (shell : Shell) →
      Ordered.OrderedMonoid._≤_ O
        (outputEnergy shell)
        (envelope (localPrefactor shell) shell)

    envelopeMonotone :
      (shell : Shell) →
      {small large : Nat} →
      small ≤ large →
      Ordered.OrderedMonoid._≤_ O
        (envelope small shell)
        (envelope large shell)

open PrefactorEnergyData public

pointwiseGlobalPrefactorBound :
  ∀ {ℓ s}
    (data : PrefactorEnergyData {ℓ} {s}) →
    (shell : Shell data) →
  Ordered.OrderedMonoid._≤_ (O data)
    (outputEnergy data shell)
    (envelope data (globalPrefactor data) shell)
pointwiseGlobalPrefactorBound data shell =
  Ordered.OrderedMonoid.trans≤ (O data)
    _ _ _
    (localBound data shell)
    (envelopeMonotone data shell
      (localPrefactor≤global data shell))

assembleGlobalPrefactorBound :
  ∀ {ℓ s}
    (data : PrefactorEnergyData {ℓ} {s}) →
  Ordered.OrderedMonoid._≤_ (O data)
    (sumBy (O data) (outputEnergy data) (shells data))
    (sumBy (O data)
      (envelope data (globalPrefactor data))
      (shells data))
assembleGlobalPrefactorBound data = go (shells data)
  where
  go :
    (remaining : List (Shell data)) →
    Ordered.OrderedMonoid._≤_ (O data)
      (sumBy (O data) (outputEnergy data) remaining)
      (sumBy (O data)
        (envelope data (globalPrefactor data))
        remaining)
  go [] = Ordered.OrderedMonoid.refl≤ (O data) (0# (M (O data)))
  go (shell ∷ remaining) =
    Ordered.OrderedMonoid.mono+ (O data)
      _ _ _ _
      (pointwiseGlobalPrefactorBound data shell)
      (go remaining)
