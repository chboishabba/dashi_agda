module DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyControlledFarTailExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Derive the finite energy-controlled far-history estimate in the exact
-- dyadic heat model.  A terminal gap contributes h(gap), every older time
-- layer contributes another factor 1/2, and a common energy envelope E gives
--
--   farTail(E,gap,N)
--     = E h(gap) sum_{j=0}^N (1/2)^j
--     <= 2 E h(gap).
--
-- Unlike the conditional turbulent-tail criterion, no lower bound on the
-- high-frequency seed is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact as Heat

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

oneMinusHalfPositive : 0ℚ < 1ℚ - half
oneMinusHalfPositive = toWitness {a? = 0ℚ <? 1ℚ - half} _

halfBoundIdentity :
  (1ℚ - half) * two ≡ 1ℚ
halfBoundIdentity = refl

farTail : ℚ → Nat → Nat → ℚ
farTail energy terminalGap zero =
  energy * Heat.heatDamping terminalGap
farTail energy terminalGap (suc cutoff) =
  energy * Heat.heatDamping (terminalGap + suc cutoff)
  + farTail energy terminalGap cutoff

farTailExactFactorisation :
  (energy : ℚ) →
  (terminalGap cutoff : Nat) →
  farTail energy terminalGap cutoff
  ≡ (energy * Heat.heatDamping terminalGap)
      * Geo.partialSum half cutoff
farTailExactFactorisation energy terminalGap zero =
  solve (energy ∷ Heat.heatDamping terminalGap ∷ [])
farTailExactFactorisation energy terminalGap (suc cutoff)
  rewrite Heat.heatSemigroup terminalGap (suc cutoff)
        | farTailExactFactorisation energy terminalGap cutoff =
  solve
    ( energy
    ∷ Heat.heatDamping terminalGap
    ∷ Geo.pow half (suc cutoff)
    ∷ Geo.partialSum half cutoff
    ∷ []
    )

farTailBound :
  (energy : ℚ) →
  0ℚ ≤ energy →
  (terminalGap cutoff : Nat) →
  farTail energy terminalGap cutoff
  ≤ two * energy * Heat.heatDamping terminalGap
farTailBound energy energyNonnegative terminalGap cutoff =
  let
    base = energy * Heat.heatDamping terminalGap

    heatNonnegative : 0ℚ ≤ Heat.heatDamping terminalGap
    heatNonnegative =
      Geo.powNonnegative half terminalGap halfNonnegative

    baseNonnegative : 0ℚ ≤ base
    baseNonnegative =
      let
        instance
          energyIsNonnegative = nonNegative energyNonnegative
          heatIsNonnegative = nonNegative heatNonnegative
          baseIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              energy (Heat.heatDamping terminalGap)
      in
      ℚₚ.nonNegative⁻¹ base

    geometricBound : Geo.partialSum half cutoff ≤ two
    geometricBound =
      Geo.geometricPartialSumBound
        half two cutoff
        halfNonnegative oneMinusHalfPositive halfBoundIdentity

    scaled :
      base * Geo.partialSum half cutoff ≤ base * two
    scaled =
      let
        instance baseIsNonnegative = nonNegative baseNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg base geometricBound

    targetMeaning : base * two ≡ two * energy * Heat.heatDamping terminalGap
    targetMeaning = solve (energy ∷ Heat.heatDamping terminalGap ∷ two ∷ [])
  in
  subst
    (λ upper → farTail energy terminalGap cutoff ≤ upper)
    targetMeaning
    (subst
      (λ lower → lower ≤ base * two)
      (sym (farTailExactFactorisation energy terminalGap cutoff))
      scaled)
