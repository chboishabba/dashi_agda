module DASHI.Physics.Closure.NSTriadKNCanonicalTriadOrbitEnumeration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Bool.Base using (T)
open import Data.List.Base using (List; []; _∷_; cartesianProductWith; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable.Core using (T?)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactLatticeTriadZeroSum as ZeroSum
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

-- Unlike the labelled-output convolution carrier, the full symmetric cutoff
-- is closed under every generator of a physical triad orbit.  These are
-- concrete finite facts, derived from the cutoff decoder and zero-sum
-- algebra; they are not fields of the still-open representative-enumeration
-- contract below.
fullCutoffZeroSumTriadCycle :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  FullCutoffZeroSumTriad R τ →
  FullCutoffZeroSumTriad R (Lattice.triadCycle τ)
fullCutoffZeroSumTriadCycle R (Lattice.mkLatticeTriad left right out)
  (left∈ , (right∈ , (out∈ , zeroSum))) =
  right∈ , (out∈ , (left∈ , ZeroSum.zeroSumCycle
    (Lattice.mkLatticeTriad left right out) zeroSum))

fullCutoffZeroSumTriadSwap :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  FullCutoffZeroSumTriad R τ →
  FullCutoffZeroSumTriad R (Lattice.triadSwap τ)
fullCutoffZeroSumTriadSwap R (Lattice.mkLatticeTriad left right out)
  (left∈ , (right∈ , (out∈ , zeroSum))) =
  right∈ , (left∈ , (out∈ , ZeroSum.zeroSumSwap
    (Lattice.mkLatticeTriad left right out) zeroSum))

fullCutoffZeroSumTriadNeg :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  FullCutoffZeroSumTriad R τ →
  FullCutoffZeroSumTriad R (Lattice.triadNeg τ)
fullCutoffZeroSumTriadNeg R (Lattice.mkLatticeTriad left right out)
  (left∈ , (right∈ , (out∈ , zeroSum))) =
  Sector.cutoffModesNeg R left left∈ ,
  (Sector.cutoffModesNeg R right right∈ ,
   (Sector.cutoffModesNeg R out out∈ , ZeroSum.zeroSumNeg
     (Lattice.mkLatticeTriad left right out) zeroSum))

record FullCutoffPermutationRealityClosure (R : Nat) : Set where
  field
    cyclePreserves :
      (τ : Lattice.LatticeTriad) → FullCutoffZeroSumTriad R τ →
      FullCutoffZeroSumTriad R (Lattice.triadCycle τ)
    swapPreserves :
      (τ : Lattice.LatticeTriad) → FullCutoffZeroSumTriad R τ →
      FullCutoffZeroSumTriad R (Lattice.triadSwap τ)
    realityPreserves :
      (τ : Lattice.LatticeTriad) → FullCutoffZeroSumTriad R τ →
      FullCutoffZeroSumTriad R (Lattice.triadNeg τ)

fullCutoffPermutationRealityClosure :
  (R : Nat) → FullCutoffPermutationRealityClosure R
fullCutoffPermutationRealityClosure R = record
  { cyclePreserves = fullCutoffZeroSumTriadCycle R
  ; swapPreserves = fullCutoffZeroSumTriadSwap R
  ; realityPreserves = fullCutoffZeroSumTriadNeg R
  }

fullCutoffZeroSumTriads : Nat → List Lattice.LatticeTriad
fullCutoffZeroSumTriads R =
  filterᵇ Lattice.zeroSum?
    (cartesianProductWith
      (λ left pair → Lattice.mkLatticeTriad left (proj₁ pair)
        (proj₂ pair))
      (Sector.cutoffModes R)
      (cartesianProductWith _,_ (Sector.cutoffModes R) (Sector.cutoffModes R)))

boolTrueFromT : {b : Bool} → T b → b ≡ true
boolTrueFromT {true} _ = refl
boolTrueFromT {false} ()

tFromBoolTrue : {b : Bool} → b ≡ true → T b
tFromBoolTrue {true} _ = _
tFromBoolTrue {false} ()

fullCutoffCandidateMember :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  FullCutoffZeroSumTriad R τ →
  τ ∈ cartesianProductWith
    (λ left pair → Lattice.mkLatticeTriad left (proj₁ pair) (proj₂ pair))
    (Sector.cutoffModes R)
    (cartesianProductWith _,_ (Sector.cutoffModes R) (Sector.cutoffModes R))
fullCutoffCandidateMember R (Lattice.mkLatticeTriad left right out)
  (left∈ , (right∈ , (out∈ , zeroSum))) =
  ∈-cartesianProductWith⁺
    (λ left pair → Lattice.mkLatticeTriad left (proj₁ pair) (proj₂ pair))
    left∈
    (∈-cartesianProductWith⁺ _,_ right∈ out∈)

fullCutoffCandidateMembership :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ cartesianProductWith
    (λ left pair → Lattice.mkLatticeTriad left (proj₁ pair) (proj₂ pair))
    (Sector.cutoffModes R)
    (cartesianProductWith _,_ (Sector.cutoffModes R) (Sector.cutoffModes R)) →
  (Lattice.left τ ∈ Sector.cutoffModes R) ×
  ((Lattice.right τ ∈ Sector.cutoffModes R) ×
   (Lattice.out τ ∈ Sector.cutoffModes R))
fullCutoffCandidateMembership R τ τ∈candidates
  with ∈-cartesianProductWith⁻
    (λ left pair → Lattice.mkLatticeTriad left (proj₁ pair) (proj₂ pair))
    (Sector.cutoffModes R)
    (cartesianProductWith _,_ (Sector.cutoffModes R) (Sector.cutoffModes R))
    τ∈candidates
... | left , pair , left∈ , pair∈ , τ≡
  with ∈-cartesianProductWith⁻ _,_ (Sector.cutoffModes R) (Sector.cutoffModes R) pair∈
... | right , out , right∈ , out∈ , pair≡
  rewrite τ≡ | pair≡ = left∈ , (right∈ , out∈)

fullCutoffZeroSumTriadsSound :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  τ ∈ fullCutoffZeroSumTriads R → FullCutoffZeroSumTriad R τ
fullCutoffZeroSumTriadsSound R τ τ∈
  with ∈-filter⁻ (T? ∘ Lattice.zeroSum?) τ∈
... | τ∈candidates , zeroSum =
  let modes = fullCutoffCandidateMembership R τ τ∈candidates in
  proj₁ modes , (proj₁ (proj₂ modes) ,
    (proj₂ (proj₂ modes) , boolTrueFromT zeroSum))

fullCutoffZeroSumTriadsComplete :
  (R : Nat) → (τ : Lattice.LatticeTriad) →
  FullCutoffZeroSumTriad R τ → τ ∈ fullCutoffZeroSumTriads R
fullCutoffZeroSumTriadsComplete R τ τ∈ =
  ∈-filter⁺ (T? ∘ Lattice.zeroSum?)
    (fullCutoffCandidateMember R τ τ∈)
    (substT τ∈)
  where
  substT : FullCutoffZeroSumTriad R τ → T (Lattice.zeroSum? τ)
  substT (_ , (_ , (_ , zeroSum))) = tFromBoolTrue zeroSum

FullCutoffCanonicalTriadOrbitEnumeration : Nat → Set₁
FullCutoffCanonicalTriadOrbitEnumeration R =
  CanonicalTriadOrbitEnumeration (FullCutoffZeroSumTriad R)

canonicalTriadOrbitEnumerationClosed : Bool
canonicalTriadOrbitEnumerationClosed = false
