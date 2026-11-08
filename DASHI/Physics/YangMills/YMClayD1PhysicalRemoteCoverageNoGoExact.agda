{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayD1PhysicalRemoteCoverageNoGoExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE D1 GATE: PHYSICAL REMOTE PAIR COVERAGE IS NOT OPTIONAL
--
-- The existing OriginalPhysicalCubeConditionals quantifies its uniform
-- influence premise over an arbitrary AdmissiblePerturbation predicate.
-- Instantiating that predicate to Bottom makes both original influence
-- and "uniform" inequalities vacuous, independent of original Gibbs data.
--
-- This source proves the no-go *and* a sound strengthened consumer:
-- RequiredPhysicalRemotePair must be fixed by original physical geometry;
-- all required pairs must be admissible in the *same* Gibbs source;
-- the required class must contain a distinct pair at some inhabited
-- physical cutoff and volume. The strengthened theorem transports
-- the original genuine row and observable estimate to EVERY required
-- physical boundary pair. This is still one-step local influence,
-- NOT spatial clustering, original large-field or a Clay mass gap.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; ∣_∣; _-_; _*_)
import DASHI.Physics.YangMills.YMClayPhysicalCubeDobrushinFromGibbsExact as Cube
import DASHI.Physics.YangMills.BalabanFiniteBoundaryConditionedDobrushinExact as Boundary

emptyRemotePerturbation :
  ∀ {Cutoff Volume : Set}
    {BoundaryState : Cutoff → Volume → Set}
    (cutoff : Cutoff) (volume : Volume) →
    BoundaryState cutoff volume → BoundaryState cutoff volume → Set
emptyRemotePerturbation cutoff volume left right = ⊥

arbitraryEstimateFromEmptyRemoteClass :
  ∀ {Cutoff Volume : Set}
    {BoundaryState : Cutoff → Volume → Set}
    (cutoff : Cutoff) (volume : Volume)
    (left right : BoundaryState cutoff volume)
    (Estimate : Set) →
    emptyRemotePerturbation cutoff volume left right → Estimate
arbitraryEstimateFromEmptyRemoteClass cutoff volume left right
    Estimate impossible = ⊥-elim impossible

module Selected
    {Cutoff Volume : Set}
    (Local : Cutoff → Set)
    (BoundaryState : (cutoff : Cutoff) → Volume → Set)
    (AdmissiblePerturbation :
      (cutoff : Cutoff) (volume : Volume) →
      BoundaryState cutoff volume → BoundaryState cutoff volume → Set)
    (physical : Cube.OriginalPhysicalCubeConditionals
      Cutoff Volume Local BoundaryState AdmissiblePerturbation)
    (RequiredPhysicalRemotePair :
      (cutoff : Cutoff) (volume : Volume) →
      BoundaryState cutoff volume → BoundaryState cutoff volume → Set)
  where

  record ActualPhysicalPairCoverage : Set₁ where
    field
      -- Original physical supports/boundary geometry determine REQUIRED,
      -- not an arbitrary convenient finite test-pair predicate.
      requiredAreAdmissible :
        ∀ cutoff volume (left right : BoundaryState cutoff volume) →
        RequiredPhysicalRemotePair cutoff volume left right →
        AdmissiblePerturbation cutoff volume left right

      -- Non-vacuous physical test, at one genuinely inhabited cutoff
      -- and volume, with TWO DISTINCT boundary conditions.
      selectedCutoff : Cutoff
      selectedVolume : Volume
      selectedLeft selectedRight :
        BoundaryState selectedCutoff selectedVolume
      selectedPairIsRequired :
        RequiredPhysicalRemotePair selectedCutoff selectedVolume
          selectedLeft selectedRight
      selectedPairIsDistinct : selectedLeft ≡ selectedRight → ⊥
  open ActualPhysicalPairCoverage public

  requiredOriginalConditionalRowsUniformlyContract :
    (coverage : ActualPhysicalPairCoverage) →
    ∀ cutoff volume (left right : BoundaryState cutoff volume) →
    RequiredPhysicalRemotePair cutoff volume left right →
    Boundary.conditionalRowL1
      (Cube.originalFibre physical cutoff volume) left right
    ≤ Cube.commonBlockInfluence physical
  requiredOriginalConditionalRowsUniformlyContract coverage
      cutoff volume left right physicalPair =
    Cube.originalConditionalRowsUniformlyContract physical
      cutoff volume left right
      (requiredAreAdmissible coverage cutoff volume left right physicalPair)

  requiredOriginalConditionalObservablesUniformlyContract :
    (coverage : ActualPhysicalPairCoverage) →
    ∀ cutoff volume (left right : BoundaryState cutoff volume) →
    (perturbation : RequiredPhysicalRemotePair cutoff volume left right) →
    (observable : Local cutoff → ℚ) (majorant : ℚ) →
    0ℚ ≤ majorant →
    (∀ local → ∣ observable local ∣ ≤ majorant) →
    ∣ Boundary.conditionalExpectation
        (Cube.originalFibre physical cutoff volume) observable left
        - Boundary.conditionalExpectation
          (Cube.originalFibre physical cutoff volume) observable right ∣
      ≤ majorant * Cube.commonBlockInfluence physical
  requiredOriginalConditionalObservablesUniformlyContract
      coverage cutoff volume left right perturbation
      observable majorant nonnegative bounded =
    Cube.originalConditionalObservableUniformlyContract physical
      cutoff volume left right
      (requiredAreAdmissible coverage cutoff volume left right perturbation)
      observable majorant nonnegative bounded

  coverageCannotBeEmpty :
    (coverage : ActualPhysicalPairCoverage) →
    (∀ cutoff volume (left right : BoundaryState cutoff volume) →
      AdmissiblePerturbation cutoff volume left right → ⊥) → ⊥
  coverageCannotBeEmpty coverage rejects =
    rejects
      (selectedCutoff coverage) (selectedVolume coverage)
      (selectedLeft coverage) (selectedRight coverage)
      (requiredAreAdmissible coverage
        (selectedCutoff coverage) (selectedVolume coverage)
        (selectedLeft coverage) (selectedRight coverage)
        (selectedPairIsRequired coverage))
