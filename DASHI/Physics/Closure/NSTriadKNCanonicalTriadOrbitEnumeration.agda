module DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumeration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.List.Base using (List; []; _∷_; cartesianProductWith; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Canonical permutation/reality orbit enumeration.
--
-- The finite physical packet fold is meaningful only when every retained
-- zero-sum triad is represented once modulo all leg permutations and the
-- reality partner.  This module makes that missing finite combinatorial
-- theorem explicit.  It does not assert that the current lattice enumerator
-- has been quotiented; `canonicalTriadOrbitEnumerationClosed` remains false.
------------------------------------------------------------------------

triadCycleTwice : Lattice.LatticeTriad → Lattice.LatticeTriad
triadCycleTwice τ = Lattice.triadCycle (Lattice.triadCycle τ)

-- Six leg permutations followed by the corresponding six reality partners.
-- Membership of this finite list is the concrete equivalence relation used by
-- the canonical packet-transfer fold; no ordering on lattice modes is needed.
canonicalOrbitMembers : Lattice.LatticeTriad → List Lattice.LatticeTriad
canonicalOrbitMembers τ =
  τ ∷
  Lattice.triadSwap τ ∷
  Lattice.triadCycle τ ∷
  Lattice.triadSwap (Lattice.triadCycle τ) ∷
  triadCycleTwice τ ∷
  Lattice.triadSwap (triadCycleTwice τ) ∷
  Lattice.triadNeg τ ∷
  Lattice.triadNeg (Lattice.triadSwap τ) ∷
  Lattice.triadNeg (Lattice.triadCycle τ) ∷
  Lattice.triadNeg (Lattice.triadSwap (Lattice.triadCycle τ)) ∷
  Lattice.triadNeg (triadCycleTwice τ) ∷
  Lattice.triadNeg (Lattice.triadSwap (triadCycleTwice τ)) ∷
  []

SameCanonicalTriadOrbit :
  Lattice.LatticeTriad → Lattice.LatticeTriad → Set
SameCanonicalTriadOrbit τ σ = τ ∈ canonicalOrbitMembers σ

record CanonicalTriadOrbitEnumeration
    (Retained : Lattice.LatticeTriad → Set) : Set₁ where
  field
    representatives : List Energy.ZeroSumTriad

    representativeRetained :
      (σ : Energy.ZeroSumTriad) → σ ∈ representatives →
      Retained (Energy.triad σ)

    everyRetainedTriadHasRepresentative :
      (τ : Lattice.LatticeTriad) → Retained τ →
      Σ Energy.ZeroSumTriad
        (λ σ → (σ ∈ representatives) × SameCanonicalTriadOrbit τ (Energy.triad σ))

    representativesSeparateOrbits :
      (σ ρ : Energy.ZeroSumTriad) → σ ∈ representatives → ρ ∈ representatives →
      SameCanonicalTriadOrbit (Energy.triad σ) (Energy.triad ρ) →
      Energy.triad σ ≡ Energy.triad ρ

open CanonicalTriadOrbitEnumeration public

-- The earlier same-shell enumeration is one specialization.  The physical
-- CFD audit instead fixes an output packet while allowing inputs throughout a
-- finite cutoff carrier, so it will instantiate the generic record with the
-- corresponding raw-cutoff/retained-sector predicate rather than this alias.
SameShellCanonicalTriadOrbitEnumeration :
  (N : Nat) → Lattice.ExactRetainedSectorLaw N → Set₁
SameShellCanonicalTriadOrbitEnumeration N sector =
  CanonicalTriadOrbitEnumeration (Lattice.RetainedTriadMember N sector)

-- This is the carrier matching the finite CFD audit more closely: all three
-- modes lie in the symmetric cutoff, while a packet multiplier decides which
-- modal legs contribute to T^K_Delta.  It is deliberately distinct from the
-- labelled-output raw convolution carrier, which cannot be cycle invariant.
FullCutoffZeroSumTriad : Nat → Lattice.LatticeTriad → Set
FullCutoffZeroSumTriad R τ =
  (Lattice.left τ ∈ Sector.cutoffModes R) ×
  ((Lattice.right τ ∈ Sector.cutoffModes R) ×
   ((Lattice.out τ ∈ Sector.cutoffModes R) ×
    (Lattice.zeroSum? τ ≡ true)))

fullCutoffZeroSumTriads : Nat → List Lattice.LatticeTriad
fullCutoffZeroSumTriads R =
  filterᵇ Lattice.zeroSum?
    (cartesianProductWith
      (λ left pair → Lattice.mkLatticeTriad left (proj₁ pair)
        (proj₂ pair))
      (Sector.cutoffModes R)
      (cartesianProductWith _,_ (Sector.cutoffModes R) (Sector.cutoffModes R)))

FullCutoffCanonicalTriadOrbitEnumeration : Nat → Set₁
FullCutoffCanonicalTriadOrbitEnumeration R =
  CanonicalTriadOrbitEnumeration (FullCutoffZeroSumTriad R)

canonicalTriadOrbitEnumerationClosed : Bool
canonicalTriadOrbitEnumerationClosed = false
