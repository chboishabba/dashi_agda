module DASHI.Physics.Closure.NSTriadKNLuoSection4PhysicalBoundsAdapterExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Require the four Section-4 estimates on explicitly named physical source
-- quantities and transport them to the exact finite J11-lower, J11-upper,
-- J12 and J2 fields. This prevents one generic nonlinear estimate from
-- silently inhabiting all four source obligations.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as Evolution
import DASHI.Physics.Closure.NSTriadKNLuoSection4ContinuityProofExact as Section4

record LuoSection4PhysicalComponentInputs
    {stateLevel scalarLevel : Level}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    (evolution : Evolution.LuoPerModeCommutatorEvolution State Scalar)
    (state : State)
    : Set (lsuc (stateLevel ⊔ scalarLevel)) where
  field
    lowModeBound highModeBound : Nat → Scalar

    physicalJ11Lower physicalJ11Upper physicalJ12 physicalJ2 :
      Nat → Scalar

    physicalJ11LowerBound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (physicalJ11Lower shell)
        (lowModeBound shell)

    physicalJ11UpperBound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (physicalJ11Upper shell)
        (highModeBound shell)

    physicalJ12Bound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (physicalJ12 shell)
        (highModeBound shell)

    physicalJ2Bound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (physicalJ2 shell)
        (highModeBound shell)

    physicalJ11LowerMatchesFiniteRange :
      (shell : Nat) →
      physicalJ11Lower shell
      ≡ Evolution.lowerHalfRange evolution shell state

    physicalJ11UpperMatchesFiniteRange :
      (shell : Nat) →
      physicalJ11Upper shell
      ≡ Evolution.upperHalfRange evolution shell state

    physicalJ12MatchesFiniteRange :
      (shell : Nat) →
      physicalJ12 shell
      ≡ Evolution.J12 evolution shell state

    physicalJ2MatchesFiniteRange :
      (shell : Nat) →
      physicalJ2 shell
      ≡ Evolution.J2 evolution shell state

open LuoSection4PhysicalComponentInputs public

section4ComponentBounds :
  ∀ {stateLevel scalarLevel}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    {evolution : Evolution.LuoPerModeCommutatorEvolution State Scalar}
    {state : State} →
  (inputs : LuoSection4PhysicalComponentInputs evolution state) →
  Section4.LuoStep1ComponentBounds
    evolution state
    (lowModeBound inputs)
    (highModeBound inputs)
section4ComponentBounds {evolution = evolution} inputs = record
  { J11LowerHalfBound = λ shell →
      subst
        (λ left → Evolution.lessOrEqual evolution left (lowModeBound inputs shell))
        (physicalJ11LowerMatchesFiniteRange inputs shell)
        (physicalJ11LowerBound inputs shell)
  ; J11UpperHalfBound = λ shell →
      subst
        (λ left → Evolution.lessOrEqual evolution left (highModeBound inputs shell))
        (physicalJ11UpperMatchesFiniteRange inputs shell)
        (physicalJ11UpperBound inputs shell)
  ; J12Bound = λ shell →
      subst
        (λ left → Evolution.lessOrEqual evolution left (highModeBound inputs shell))
        (physicalJ12MatchesFiniteRange inputs shell)
        (physicalJ12Bound inputs shell)
  ; J2Bound = λ shell →
      subst
        (λ left → Evolution.lessOrEqual evolution left (highModeBound inputs shell))
        (physicalJ2MatchesFiniteRange inputs shell)
        (physicalJ2Bound inputs shell)
  }

section4FourPhysicalBoundsSeparated : Bool
section4FourPhysicalBoundsSeparated = true

section4PhysicalToFiniteRangeAdapterClosed : Bool
section4PhysicalToFiniteRangeAdapterClosed = true

section4FourPhysicalBoundsSeparatedIsTrue :
  section4FourPhysicalBoundsSeparated ≡ true
section4FourPhysicalBoundsSeparatedIsTrue = refl

section4PhysicalToFiniteRangeAdapterClosedIsTrue :
  section4PhysicalToFiniteRangeAdapterClosed ≡ true
section4PhysicalToFiniteRangeAdapterClosedIsTrue = refl
