module DASHI.Music.MusicalSymmetryDynamicsCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Algebraic symmetry and its fixed class.
------------------------------------------------------------------------

infix 4 _≢_

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record InvolutiveSymmetry (Melody : Set) : Set₁ where
  field
    symmetry : Melody → Melody
    involutive : ∀ melody → symmetry (symmetry melody) ≡ melody

open InvolutiveSymmetry public

Symmetric :
  {Melody : Set} →
  InvolutiveSymmetry Melody →
  Melody →
  Set
Symmetric S melody =
  symmetry S melody ≡ melody

------------------------------------------------------------------------
-- Defect/energy surface.
--
-- No order, norm, or metric is smuggled in.  A domain instance supplies its
-- own energy carrier and its own comparison relation.
------------------------------------------------------------------------

record AsymmetryEnergy
    (Melody : Set)
    (S : InvolutiveSymmetry Melody) : Set₁ where
  field
    Energy : Set
    zeroEnergy : Energy
    energyOrder : Energy → Energy → Set
    energy : Melody → Energy

    symmetricHasZeroEnergy :
      ∀ {melody} →
      Symmetric S melody →
      energy melody ≡ zeroEnergy

    zeroEnergyIsSymmetric :
      ∀ {melody} →
      energy melody ≡ zeroEnergy →
      Symmetric S melody

open AsymmetryEnergy public

------------------------------------------------------------------------
-- Repair dynamics.
--
-- This is deliberately weaker and more honest than a global contraction
-- theorem.  The repair must land in the fixed class, fix every already-
-- symmetric melody, and not increase the supplied defect energy.
------------------------------------------------------------------------

record SymmetryRepair
    (Melody : Set)
    (S : InvolutiveSymmetry Melody)
    (E : AsymmetryEnergy Melody S) : Set₁ where
  field
    repair : Melody → Melody

    repairedIsSymmetric :
      ∀ melody →
      Symmetric S (repair melody)

    fixesSymmetric :
      ∀ {melody} →
      Symmetric S melody →
      repair melody ≡ melody

    energyDoesNotIncrease :
      ∀ melody →
      energyOrder E
        (energy E (repair melody))
        (energy E melody)

open SymmetryRepair public

repairIdempotent :
  {Melody : Set} →
  {S : InvolutiveSymmetry Melody} →
  {E : AsymmetryEnergy Melody S} →
  (R : SymmetryRepair Melody S E) →
  ∀ melody →
  repair R (repair R melody) ≡ repair R melody
repairIdempotent R melody =
  fixesSymmetric R (repairedIsSymmetric R melody)

fixedRepairIsSymmetric :
  {Melody : Set} →
  {S : InvolutiveSymmetry Melody} →
  {E : AsymmetryEnergy Melody S} →
  (R : SymmetryRepair Melody S E) →
  ∀ {melody} →
  repair R melody ≡ melody →
  Symmetric S melody
fixedRepairIsSymmetric {S = S} R {melody} fixed =
  trans
    (sym (cong (symmetry S) fixed))
    (trans
      (repairedIsSymmetric R melody)
      fixed)

repairFixedPointIffSymmetricForward :
  {Melody : Set} →
  {S : InvolutiveSymmetry Melody} →
  {E : AsymmetryEnergy Melody S} →
  (R : SymmetryRepair Melody S E) →
  ∀ {melody} →
  repair R melody ≡ melody →
  Symmetric S melody
repairFixedPointIffSymmetricForward =
  fixedRepairIsSymmetric

repairFixedPointIffSymmetricBackward :
  {Melody : Set} →
  {S : InvolutiveSymmetry Melody} →
  {E : AsymmetryEnergy Melody S} →
  (R : SymmetryRepair Melody S E) →
  ∀ {melody} →
  Symmetric S melody →
  repair R melody ≡ melody
repairFixedPointIffSymmetricBackward R =
  fixesSymmetric R

------------------------------------------------------------------------
-- Basin assignment and finite volume surface.
--
-- Basin volume is kept separate from the repair theorem.  A finite enumerator
-- or empirical diagnostic may fill this surface, but fixed-point structure by
-- itself does not imply a cognitive preference.
------------------------------------------------------------------------

record AttractorAssignment (State Attractor : Set) : Set₁ where
  field
    attractorOf : State → Attractor
    realize : Attractor → State
    realizedAttractorIsFixed :
      ∀ attractor →
      attractorOf (realize attractor) ≡ attractor

open AttractorAssignment public

Basin :
  {State Attractor : Set} →
  AttractorAssignment State Attractor →
  Attractor →
  State →
  Set
Basin assignment attractor state =
  attractorOf assignment state ≡ attractor

record FiniteBasinMeasurement (Attractor : Set) : Set₁ where
  field
    basinVolume : Attractor → Nat
    measuredStateCount : Nat

open FiniteBasinMeasurement public
