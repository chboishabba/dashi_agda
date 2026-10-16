module DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryProjectionCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Generic same-object projection compiler.
--
-- This is the mathematically required bridge from a continuum/Hilbert-space
-- Hamiltonian symmetry to a selected finite orbital/CI carrier.  It prevents
-- the common error "continuum H is symmetric, therefore my arbitrary finite
-- matrix is symmetric" unless the inclusion/projection maps themselves are
-- action-equivariant on the same state.
------------------------------------------------------------------------

record SymmetryProjectionCompiler : Set₁ where
  field
    ContinuumState : Set
    SelectedState : Set

    continuumAction : ContinuumState -> ContinuumState
    selectedAction : SelectedState -> SelectedState

    continuumHamiltonian : ContinuumState -> ContinuumState
    selectedHamiltonian : SelectedState -> SelectedState

    include : SelectedState -> ContinuumState
    project : ContinuumState -> SelectedState

    continuumCommutes :
      (x : ContinuumState) ->
      continuumHamiltonian (continuumAction x)
      ≡ continuumAction (continuumHamiltonian x)

    inclusionEquivariant :
      (x : SelectedState) ->
      include (selectedAction x)
      ≡ continuumAction (include x)

    projectionEquivariant :
      (x : ContinuumState) ->
      project (continuumAction x)
      ≡ selectedAction (project x)

    selectedHamiltonianIsProjected :
      (x : SelectedState) ->
      selectedHamiltonian x
      ≡ project (continuumHamiltonian (include x))

open SymmetryProjectionCompiler public

selectedHamiltonianCommutes :
  (C : SymmetryProjectionCompiler) ->
  (x : SelectedState C) ->
  selectedHamiltonian C (selectedAction C x)
  ≡ selectedAction C (selectedHamiltonian C x)
selectedHamiltonianCommutes C x =
  begin
    selectedHamiltonian C (selectedAction C x)
      ≡⟨ selectedHamiltonianIsProjected C (selectedAction C x) ⟩
    project C (continuumHamiltonian C (include C (selectedAction C x)))
      ≡⟨ cong (λ y -> project C (continuumHamiltonian C y))
              (inclusionEquivariant C x) ⟩
    project C (continuumHamiltonian C (continuumAction C (include C x)))
      ≡⟨ cong (project C) (continuumCommutes C (include C x)) ⟩
    project C (continuumAction C (continuumHamiltonian C (include C x)))
      ≡⟨ projectionEquivariant C (continuumHamiltonian C (include C x)) ⟩
    selectedAction C (project C (continuumHamiltonian C (include C x)))
      ≡⟨ cong (selectedAction C)
              (sym (selectedHamiltonianIsProjected C x)) ⟩
    selectedAction C (selectedHamiltonian C x)
  ∎

record SymmetryProjectionBoundary : Set where
  constructor symmetryProjectionBoundary
  field
    continuumCommutationSufficientGivenEquivariantProjection : Bool
    inclusionEquivarianceRequired : Bool
    projectionEquivarianceRequired : Bool
    sameObjectSelectedHamiltonianEqualityRequired : Bool
    arbitraryTruncationInheritsSymmetryAutomatically : Bool
    sameDimensionCreatesProjectionReceipt : Bool

open SymmetryProjectionBoundary public

canonicalSymmetryProjectionBoundary : SymmetryProjectionBoundary
canonicalSymmetryProjectionBoundary =
  symmetryProjectionBoundary true true true true false false

arbitraryTruncationDoesNotInheritSymmetry :
  arbitraryTruncationInheritsSymmetryAutomatically canonicalSymmetryProjectionBoundary
  ≡ false
arbitraryTruncationDoesNotInheritSymmetry = refl
