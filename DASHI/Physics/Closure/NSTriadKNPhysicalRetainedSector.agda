module DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Bool.Base using (_∧_)
open import Data.Integer.Base as ℤ using (ℤ; +_)
open import Data.List.Base using (List; cartesianProductWith; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice

------------------------------------------------------------------------
-- Exact labelled-output retained sector for the periodic Fourier
-- convolution.  Unlike a same-shell triad sector, this is deliberately not
-- cycle invariant: `out` is the distinguished output mode in shell N and
-- `left`, `right` are the two cutoff input modes.  Input swap and reality are
-- the relevant symmetries for the unordered-pair interaction convention.
------------------------------------------------------------------------

cutoffModes : Nat → List Lattice.LatticeMode3
cutoffModes R =
  filterᵇ Lattice.nonzeroMode?
    (Data.List.Base.map (Lattice.decodeCubeCode R) (Lattice.cubeCodes R))

-- Membership in `cutoffModes R` is the computational cutoff predicate.  It
-- is deliberately list-based here: a coordinate inequality formulation must
-- include both lower and upper signed bounds.
coordinateInCutoff? : Nat → ℤ → Bool
coordinateInCutoff? R z =
  ((ℤ.- (+ R)) ℤ.≤ᵇ z) ∧ (z ℤ.≤ᵇ (+ R))

inExactCutoff? : Nat → Lattice.LatticeMode3 → Bool
inExactCutoff? R k =
  Lattice.nonzeroMode? k ∧
  (coordinateInCutoff? R (Lattice.k₁ k) ∧
   (coordinateInCutoff? R (Lattice.k₂ k) ∧
    coordinateInCutoff? R (Lattice.k₃ k)))

physicalRetainedSector? : Nat → Nat → Lattice.LatticeTriad → Bool
physicalRetainedSector? N R τ =
  Lattice.zeroSum? τ ∧
  (Lattice.inExactShell? N (Lattice.out τ) ∧
   (inExactCutoff? R (Lattice.left τ) ∧ inExactCutoff? R (Lattice.right τ)))

record ExactOutputRetainedSectorLaw (N R : Nat) : Set₁ where
  field
    retained? : Lattice.LatticeTriad → Bool
    inputSwapInvariant :
      (τ : Lattice.LatticeTriad) → retained? (Lattice.triadSwap τ) ≡ retained? τ
    realityInvariant :
      (τ : Lattice.LatticeTriad) → retained? (Lattice.triadNeg τ) ≡ retained? τ
    zeroSumRequired :
      (τ : Lattice.LatticeTriad) → retained? τ ≡ true → Lattice.zeroSum? τ ≡ true
    outputShellRequired :
      (τ : Lattice.LatticeTriad) → retained? τ ≡ true →
      Lattice.inExactShell? N (Lattice.out τ) ≡ true

open ExactOutputRetainedSectorLaw public

physicalOutputSectorCandidates : Nat → Nat → List Lattice.LatticeTriad
physicalOutputSectorCandidates N R =
  cartesianProductWith
    (λ left pair → Lattice.mkLatticeTriad left
      (Data.Product.proj₁ pair) (Data.Product.proj₂ pair))
    (cutoffModes R)
    (cartesianProductWith _,_ (cutoffModes R) (Lattice.exactShellModes N))

exactCutoffRetainedTriads :
  (N R : Nat) → ExactOutputRetainedSectorLaw N R → List Lattice.LatticeTriad
exactCutoffRetainedTriads N R sector =
  filterᵇ (retained? sector) (physicalOutputSectorCandidates N R)

OutputRetainedTriadMember :
  (N R : Nat) → ExactOutputRetainedSectorLaw N R → Lattice.LatticeTriad → Set
OutputRetainedTriadMember N R sector τ =
  τ ∈ exactCutoffRetainedTriads N R sector

-- The following is the exact PDE-facing enumeration obligation.  It includes
-- the completeness statement within a finite cutoff and leaves the R → ∞
-- passage explicitly downstream.
record ExactCutoffRetainedTriadEnumeration
    (N R : Nat) (sector : ExactOutputRetainedSectorLaw N R) : Set₁ where
  field
    triads : List Lattice.LatticeTriad
    triadsAreExact : triads ≡ exactCutoffRetainedTriads N R sector
    sound : (τ : Lattice.LatticeTriad) → τ ∈ triads → retained? sector τ ≡ true
    completeWithinCutoff :
      (τ : Lattice.LatticeTriad) →
      τ ∈ physicalOutputSectorCandidates N R → retained? sector τ ≡ true → τ ∈ triads

physicalOutputSectorClosed : Bool
physicalOutputSectorClosed = false
