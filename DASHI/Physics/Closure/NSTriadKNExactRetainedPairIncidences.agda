module DASHI.Physics.Closure.NSTriadKNExactRetainedPairIncidences where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Fiber
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as PhysicalSector

------------------------------------------------------------------------
-- Canonical pair-incidence carrier for the weighted pair-Laplacian.
--
-- The executable diagnostic expands each triad into the three unordered
-- pairs (left,right), (left,out), and (right,out), and applies the signed
-- edge vector e_source - e_target.  This module makes that multiplicity
-- and orientation explicit before any Gram form is assembled.
------------------------------------------------------------------------

PairSlot : Set
PairSlot = Fiber.PairSlot

open Fiber.PairSlot public

pairSlots : List PairSlot
pairSlots = firstPair ∷ secondPair ∷ thirdPair ∷ []

pairSlotsHaveThreeEntries :
  pairSlots ≡ firstPair ∷ secondPair ∷ thirdPair ∷ []
pairSlotsHaveThreeEntries = refl

record PairIncidence : Set where
  constructor mkPairIncidence
  field
    triad : Shell.LatticeTriad
    slot  : PairSlot

open PairIncidence public

sourceMode : PairIncidence → Shell.LatticeMode3
sourceMode (mkPairIncidence τ firstPair) = Shell.left τ
sourceMode (mkPairIncidence τ secondPair) = Shell.left τ
sourceMode (mkPairIncidence τ thirdPair) = Shell.right τ

targetMode : PairIncidence → Shell.LatticeMode3
targetMode (mkPairIncidence τ firstPair) = Shell.right τ
targetMode (mkPairIncidence τ secondPair) = Shell.out τ
targetMode (mkPairIncidence τ thirdPair) = Shell.out τ

remainingMode : PairIncidence → Shell.LatticeMode3
remainingMode (mkPairIncidence τ firstPair) = Shell.out τ
remainingMode (mkPairIncidence τ secondPair) = Shell.right τ
remainingMode (mkPairIncidence τ thirdPair) = Shell.left τ

-- This orientation is the one actually used by the matrix-free executor:
-- ``x[source] - x[target]``.  Reversing it changes b to -b, hence leaves
-- the rank-one Laplacian b bᵀ unchanged, but it must still be fixed once.
data EdgeOrientation : Set where
  sourceMinusTarget : EdgeOrientation

orientation : PairIncidence → EdgeOrientation
orientation _ = sourceMinusTarget

pairIncidencesFor : Shell.LatticeTriad → List PairIncidence
pairIncidencesFor τ =
  mkPairIncidence τ firstPair ∷
  mkPairIncidence τ secondPair ∷
  mkPairIncidence τ thirdPair ∷ []

pairIncidencesForHasThreeSlots :
  (τ : Shell.LatticeTriad) →
  pairIncidencesFor τ ≡
    mkPairIncidence τ firstPair ∷
    mkPairIncidence τ secondPair ∷
    mkPairIncidence τ thirdPair ∷ []
pairIncidencesForHasThreeSlots τ = refl

expandTriads : List Shell.LatticeTriad → List PairIncidence
expandTriads [] = []
expandTriads (τ ∷ τs) = pairIncidencesFor τ ++ expandTriads τs

exactRetainedPairIncidences :
  (N : Nat) → (sector : Shell.ExactRetainedSectorLaw N) →
  List PairIncidence
exactRetainedPairIncidences N sector =
  expandTriads (Shell.exactRetainedTriads N sector)

------------------------------------------------------------------------
-- Physical cutoff-sector specialization.
--
-- The legacy `exactRetainedPairIncidences` list is parameterized by the
-- cycle-symmetric same-shell sector.  Fourier convolution instead has a
-- distinguished output shell and two cutoff inputs, so it receives this
-- separate list.  Both use the identical three-slot expansion; neither is
-- identified with the other.
------------------------------------------------------------------------

physicalCutoffRetainedPairIncidences :
  (N R : Nat) →
  PhysicalSector.ExactOutputRetainedSectorLaw N R →
  List PairIncidence
physicalCutoffRetainedPairIncidences N R sector =
  expandTriads (PhysicalSector.exactCutoffRetainedTriads N R sector)

PhysicalCutoffPairIncidenceMember :
  (N R : Nat) →
  (sector : PhysicalSector.ExactOutputRetainedSectorLaw N R) →
  PairIncidence → Set
PhysicalCutoffPairIncidenceMember N R sector r =
  PhysicalSector.OutputRetainedTriadMember N R sector (triad r) ×
  slot r ∈ pairSlots

record ExactCutoffRetainedPairIncidenceEnumeration
    (N R : Nat)
    (sector : PhysicalSector.ExactOutputRetainedSectorLaw N R) : Set₁ where
  field
    incidences : List PairIncidence
    incidencesAreExact :
      incidences ≡ physicalCutoffRetainedPairIncidences N R sector
    sound :
      (r : PairIncidence) → r ∈ incidences →
      PhysicalCutoffPairIncidenceMember N R sector r
    completeWithinCutoff :
      (r : PairIncidence) →
      PhysicalCutoffPairIncidenceMember N R sector r → r ∈ incidences
    noDuplicates : Unique incidences

open ExactCutoffRetainedPairIncidenceEnumeration public

PairIncidenceMember :
  (N : Nat) → (sector : Shell.ExactRetainedSectorLaw N) →
  PairIncidence → Set
PairIncidenceMember N sector r =
  Shell.RetainedTriadMember N sector (triad r) × slot r ∈ pairSlots

record ExactRetainedPairIncidenceEnumeration
    (N : Nat) (sector : Shell.ExactRetainedSectorLaw N) : Set₁ where
  field
    incidences : List PairIncidence
    incidencesAreExact :
      incidences ≡ exactRetainedPairIncidences N sector
    incidenceEnumerationSound :
      (r : PairIncidence) → r ∈ incidences → PairIncidenceMember N sector r
    incidenceEnumerationComplete :
      (r : PairIncidence) → PairIncidenceMember N sector r → r ∈ incidences
    incidenceEnumerationNoDuplicates : Unique incidences

    -- The exact multiplicity statement is deliberately a theorem obligation.
    -- It cannot be discharged until the retained-triad enumeration itself is
    -- proved sound, complete, and duplicate-free.
    eachRetainedTriadContributesExactlyThreeSlots :
      (τ : Shell.LatticeTriad) →
      Shell.RetainedTriadMember N sector τ →
      (mkPairIncidence τ firstPair ∈ incidences) ×
      ((mkPairIncidence τ secondPair ∈ incidences) ×
       (mkPairIncidence τ thirdPair ∈ incidences))

open ExactRetainedPairIncidenceEnumeration public

-- The list has the correct executable expansion, but its exactness theorem
-- is still fail-closed with the lattice enumeration package.
exactRetainedPairIncidencesClosed : Bool
exactRetainedPairIncidencesClosed = false
