module DASHI.Physics.Closure.NSTriadKNTriadS3RealityActionRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Peter Constantin; Ciprian Foias.
-- Title: "Navier--Stokes Equations".
-- DOI: 10.7208/chicago/9780226115498.001.0001.
--
-- DASHI CONTRIBUTION
--
-- Expose the algebra already implicit in the Round-34 12-element canonical
-- triad orbit.  The six leg permutations are represented separately from the
-- two Fourier-reality choices.  Their product action reproduces the existing
-- concrete `TriadAction` exactly:
--
--        six permutations  x  {identity,reality}.
--
-- We deliberately do not claim that every triad has a 12-element free orbit:
-- diagonal/degenerate triads may have stabilizers.  The theorem is instead an
-- exact factorization of the action witnesses and of the orbit relation used
-- by the safe representative quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumeration as Orbit
import DASHI.Physics.Closure.NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact as Safe

data PermutationAction6 : Set where
  identity swap cycle swapCycle cycleTwice swapCycleTwice : PermutationAction6

data RealityAction2 : Set where
  direct reality : RealityAction2

applyPermutation : PermutationAction6 → Lattice.LatticeTriad → Lattice.LatticeTriad
applyPermutation identity τ = τ
applyPermutation swap τ = Lattice.triadSwap τ
applyPermutation cycle τ = Lattice.triadCycle τ
applyPermutation swapCycle τ = Lattice.triadSwap (Lattice.triadCycle τ)
applyPermutation cycleTwice τ = Orbit.triadCycleTwice τ
applyPermutation swapCycleTwice τ =
  Lattice.triadSwap (Orbit.triadCycleTwice τ)

applyReality : RealityAction2 → Lattice.LatticeTriad → Lattice.LatticeTriad
applyReality direct τ = τ
applyReality reality τ = Lattice.triadNeg τ

applyFactoredAction :
  PermutationAction6 → RealityAction2 →
  Lattice.LatticeTriad → Lattice.LatticeTriad
applyFactoredAction permutation realityChoice τ =
  applyReality realityChoice (applyPermutation permutation τ)

flattenAction : PermutationAction6 → RealityAction2 → Safe.TriadAction
flattenAction identity direct = Safe.identity
flattenAction swap direct = Safe.swap
flattenAction cycle direct = Safe.cycle
flattenAction swapCycle direct = Safe.swapCycle
flattenAction cycleTwice direct = Safe.cycleTwice
flattenAction swapCycleTwice direct = Safe.swapCycleTwice
flattenAction identity reality = Safe.negIdentity
flattenAction swap reality = Safe.negSwap
flattenAction cycle reality = Safe.negCycle
flattenAction swapCycle reality = Safe.negSwapCycle
flattenAction cycleTwice reality = Safe.negCycleTwice
flattenAction swapCycleTwice reality = Safe.negSwapCycleTwice

factoredActionExact :
  (permutation : PermutationAction6) →
  (realityChoice : RealityAction2) →
  (τ : Lattice.LatticeTriad) →
  applyFactoredAction permutation realityChoice τ
  ≡ Safe.applyAction (flattenAction permutation realityChoice) τ
factoredActionExact identity direct τ = refl
factoredActionExact swap direct τ = refl
factoredActionExact cycle direct τ = refl
factoredActionExact swapCycle direct τ = refl
factoredActionExact cycleTwice direct τ = refl
factoredActionExact swapCycleTwice direct τ = refl
factoredActionExact identity reality τ = refl
factoredActionExact swap reality τ = refl
factoredActionExact cycle reality τ = refl
factoredActionExact swapCycle reality τ = refl
factoredActionExact cycleTwice reality τ = refl
factoredActionExact swapCycleTwice reality τ = refl

unflattenAction : Safe.TriadAction → PermutationAction6 × RealityAction2
unflattenAction Safe.identity = identity , direct
unflattenAction Safe.swap = swap , direct
unflattenAction Safe.cycle = cycle , direct
unflattenAction Safe.swapCycle = swapCycle , direct
unflattenAction Safe.cycleTwice = cycleTwice , direct
unflattenAction Safe.swapCycleTwice = swapCycleTwice , direct
unflattenAction Safe.negIdentity = identity , reality
unflattenAction Safe.negSwap = swap , reality
unflattenAction Safe.negCycle = cycle , reality
unflattenAction Safe.negSwapCycle = swapCycle , reality
unflattenAction Safe.negCycleTwice = cycleTwice , reality
unflattenAction Safe.negSwapCycleTwice = swapCycleTwice , reality

flattenUnflatten :
  (action : Safe.TriadAction) →
  flattenAction
    (proj₁ (unflattenAction action))
    (proj₂ (unflattenAction action))
  ≡ action
flattenUnflatten Safe.identity = refl
flattenUnflatten Safe.swap = refl
flattenUnflatten Safe.cycle = refl
flattenUnflatten Safe.swapCycle = refl
flattenUnflatten Safe.cycleTwice = refl
flattenUnflatten Safe.swapCycleTwice = refl
flattenUnflatten Safe.negIdentity = refl
flattenUnflatten Safe.negSwap = refl
flattenUnflatten Safe.negCycle = refl
flattenUnflatten Safe.negSwapCycle = refl
flattenUnflatten Safe.negCycleTwice = refl
flattenUnflatten Safe.negSwapCycleTwice = refl

FactoredOrbitWitness :
  Lattice.LatticeTriad → Lattice.LatticeTriad → Set
FactoredOrbitWitness τ σ =
  Σ PermutationAction6
    (λ permutation →
      Σ RealityAction2
        (λ realityChoice →
          τ ≡ applyFactoredAction permutation realityChoice σ))

factoredWitnessImpliesCanonicalOrbit :
  ∀ {τ σ} →
  FactoredOrbitWitness τ σ →
  Orbit.SameCanonicalTriadOrbit τ σ
factoredWitnessImpliesCanonicalOrbit {τ} {σ}
    (permutation , realityChoice , equality) =
  subst
    (λ selected → selected ∈ Orbit.canonicalOrbitMembers σ)
    (sym equality)
    (subst
      (λ selected → selected ∈ Orbit.canonicalOrbitMembers σ)
      (sym (factoredActionExact permutation realityChoice σ))
      (Safe.actionInOrbit (flattenAction permutation realityChoice) σ))

canonicalOrbitImpliesFactoredWitness :
  ∀ {τ σ} →
  Orbit.SameCanonicalTriadOrbit τ σ →
  FactoredOrbitWitness τ σ
canonicalOrbitImpliesFactoredWitness {τ} {σ} same
  with Safe.memberToAction τ σ same
... | action , equality =
  let
    factor = unflattenAction action
    permutation = proj₁ factor
    realityChoice = proj₂ factor

    factoredMeaning :
      applyFactoredAction permutation realityChoice σ
      ≡ Safe.applyAction action σ
    factoredMeaning =
      trans
        (factoredActionExact permutation realityChoice σ)
        (cong
          (λ selectedAction → Safe.applyAction selectedAction σ)
          (flattenUnflatten action))
  in
  permutation , realityChoice , trans equality (sym factoredMeaning)

canonicalOrbitIffFactoredAction :
  ∀ τ σ →
  (Orbit.SameCanonicalTriadOrbit τ σ → FactoredOrbitWitness τ σ)
  × (FactoredOrbitWitness τ σ → Orbit.SameCanonicalTriadOrbit τ σ)
canonicalOrbitIffFactoredAction τ σ =
  canonicalOrbitImpliesFactoredWitness , factoredWitnessImpliesCanonicalOrbit

triadPermutationRealityFactorizationClosed : Bool
triadPermutationRealityFactorizationClosed = true

freeTwelveElementOrbitAssumed : Bool
freeTwelveElementOrbitAssumed = false

triadPermutationRealityFactorizationClosedIsTrue :
  triadPermutationRealityFactorizationClosed ≡ true
triadPermutationRealityFactorizationClosedIsTrue = refl
