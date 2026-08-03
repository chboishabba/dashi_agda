module DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact where

------------------------------------------------------------------------
-- PURPOSE
-- Select the exact physical triads contributing to the repository's hard
-- high-output Fourier projection.  The low region at shell cutoff p is the
-- squared-radius ball
--
--   |k|^2 < 4^(p+1),
--
-- and the high region is its Boolean complement.  Filtering the already exact
-- cutoff-cube triad enumeration preserves soundness, completeness and
-- duplicate freedom.  This is an exact theorem for the hard projector; a
-- separate finite-band comparison is still required for Luo's smooth
-- Littlewood--Paley projector convention.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNHardDyadicShellOwner as HardShell
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm

not : Bool → Bool
not true = false
not false = true

hardLowOutputSelect : Nat → Physical.PhysicalTriadIncidence → Bool
hardLowOutputSelect shell triad =
  Physical.natLeBool
    (suc (ModeNorm.modeNatNormSquared (Physical.k triad)))
    (HardShell.pow4 (suc shell))

hardHighOutputSelect : Nat → Physical.PhysicalTriadIncidence → Bool
hardHighOutputSelect shell triad =
  not (hardLowOutputSelect shell triad)

record HardLowOutputSelected
    (shell : Nat)
    (triad : Physical.PhysicalTriadIncidence) : Set where
  constructor low-selected
  field
    lowSelection : hardLowOutputSelect shell triad ≡ true

record HardHighOutputSelected
    (shell : Nat)
    (triad : Physical.PhysicalTriadIncidence) : Set where
  constructor high-selected
  field
    highSelection : hardHighOutputSelect shell triad ≡ true

open HardLowOutputSelected public
open HardHighOutputSelected public

lowHighDisjoint :
  ∀ {shell triad} →
  HardLowOutputSelected shell triad →
  HardHighOutputSelected shell triad →
  ⊥
lowHighDisjoint {shell} {triad} low high
  with hardLowOutputSelect shell triad
... | true with highSelection high
...   | ()
... | false with lowSelection low
...   | ()

data LowOrHigh
    (shell : Nat)
    (triad : Physical.PhysicalTriadIncidence) : Set where
  low : HardLowOutputSelected shell triad → LowOrHigh shell triad
  high : HardHighOutputSelected shell triad → LowOrHigh shell triad

lowOrHigh :
  (shell : Nat) →
  (triad : Physical.PhysicalTriadIncidence) →
  LowOrHigh shell triad
lowOrHigh shell triad with hardLowOutputSelect shell triad
... | true = low (low-selected refl)
... | false = high (high-selected refl)

filterHigh :
  Nat →
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
filterHigh shell [] = []
filterHigh shell (triad ∷ triads)
  with hardHighOutputSelect shell triad
... | true = triad ∷ filterHigh shell triads
... | false = filterHigh shell triads

hardHighPhysicalTriads :
  Nat → Nat → List Physical.PhysicalTriadIncidence
hardHighPhysicalTriads shell cubeCutoff =
  filterHigh shell (Physical.physicalTriadEnumeration cubeCutoff)

filterHighMemberWasOriginal :
  ∀ {shell triads triad} →
  Cube._∈_ triad (filterHigh shell triads) →
  Cube._∈_ triad triads
filterHighMemberWasOriginal {triads = []} ()
filterHighMemberWasOriginal {shell} {triads = head ∷ tail} member
  with hardHighOutputSelect shell head
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there (filterHighMemberWasOriginal rest)
... | false = Cube.there (filterHighMemberWasOriginal member)

filterHighSound :
  ∀ {shell triads triad} →
  Cube._∈_ triad (filterHigh shell triads) →
  HardHighOutputSelected shell triad
filterHighSound {triads = []} ()
filterHighSound {shell} {triads = head ∷ tail} member
  with hardHighOutputSelect shell head
... | true with member
...   | Cube.here refl = high-selected refl
...   | Cube.there rest = filterHighSound rest
... | false = filterHighSound member

filterHighComplete :
  ∀ {shell triads triad} →
  Cube._∈_ triad triads →
  HardHighOutputSelected shell triad →
  Cube._∈_ triad (filterHigh shell triads)
filterHighComplete {triads = []} () selected
filterHighComplete {shell} {triads = head ∷ tail}
  (Cube.here refl) selected
  with hardHighOutputSelect shell head
... | true = Cube.here refl
... | false with highSelection selected
...   | ()
filterHighComplete {shell} {triads = head ∷ tail}
  (Cube.there member) selected
  with hardHighOutputSelect shell head
... | true = Cube.there (filterHighComplete member selected)
... | false = filterHighComplete member selected

filterHighNoDuplicates :
  ∀ shell {triads} →
  Cube.NoDuplicates triads →
  Cube.NoDuplicates (filterHigh shell triads)
filterHighNoDuplicates shell Cube.unique[] = Cube.unique[]
filterHighNoDuplicates shell
  (Cube.unique∷ {x = head} {xs = tail} headFresh rest)
  with hardHighOutputSelect shell head
... | true =
  Cube.unique∷ selectedHeadFresh (filterHighNoDuplicates shell rest)
  where
  selectedHeadFresh : head Cube.∉ filterHigh shell tail
  selectedHeadFresh member =
    headFresh (filterHighMemberWasOriginal member)
... | false = filterHighNoDuplicates shell rest

hardHighPhysicalTriadSound :
  ∀ {shell cubeCutoff triad} →
  Cube._∈_ triad (hardHighPhysicalTriads shell cubeCutoff) →
  Physical.PhysicalTriadInCutoff cubeCutoff triad
hardHighPhysicalTriadSound member =
  Physical.physicalTriadEnumerationCutoffSound
    (filterHighMemberWasOriginal member)

hardHighPhysicalTriadSelectionSound :
  ∀ {shell cubeCutoff triad} →
  Cube._∈_ triad (hardHighPhysicalTriads shell cubeCutoff) →
  HardHighOutputSelected shell triad
hardHighPhysicalTriadSelectionSound = filterHighSound

hardHighPhysicalTriadSelectionComplete :
  ∀ {shell cubeCutoff triad} →
  Cube._∈_ triad (Physical.physicalTriadEnumeration cubeCutoff) →
  HardHighOutputSelected shell triad →
  Cube._∈_ triad (hardHighPhysicalTriads shell cubeCutoff)
hardHighPhysicalTriadSelectionComplete = filterHighComplete

hardHighPhysicalTriadNoDuplicates :
  (shell cubeCutoff : Nat) →
  Cube.NoDuplicates (hardHighPhysicalTriads shell cubeCutoff)
hardHighPhysicalTriadNoDuplicates shell cubeCutoff =
  filterHighNoDuplicates shell
    (Physical.physicalTriadEnumerationNoDuplicates cubeCutoff)

hardHighOutputSelectionConstructed : Bool
hardHighOutputSelectionConstructed = true

hardHighSelectionSoundComplete : Bool
hardHighSelectionSoundComplete = true

hardHighSelectionDuplicateFree : Bool
hardHighSelectionDuplicateFree = true

hardLowHighPartitionConstructed : Bool
hardLowHighPartitionConstructed = true

hardProjectorComparedWithLuoSmoothProjector : Bool
hardProjectorComparedWithLuoSmoothProjector = false

hardHighOutputSelectionConstructedIsTrue :
  hardHighOutputSelectionConstructed ≡ true
hardHighOutputSelectionConstructedIsTrue = refl

hardHighSelectionSoundCompleteIsTrue :
  hardHighSelectionSoundComplete ≡ true
hardHighSelectionSoundCompleteIsTrue = refl

hardHighSelectionDuplicateFreeIsTrue :
  hardHighSelectionDuplicateFree ≡ true
hardHighSelectionDuplicateFreeIsTrue = refl

hardLowHighPartitionConstructedIsTrue :
  hardLowHighPartitionConstructed ≡ true
hardLowHighPartitionConstructedIsTrue = refl

hardProjectorComparedWithLuoSmoothProjectorIsFalse :
  hardProjectorComparedWithLuoSmoothProjector ≡ false
hardProjectorComparedWithLuoSmoothProjectorIsFalse = refl
