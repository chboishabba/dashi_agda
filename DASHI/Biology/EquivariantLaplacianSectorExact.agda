module DASHI.Biology.EquivariantLaplacianSectorExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- General commuting-action interface.  If an operator commutes with a group
-- or symmetry action and the action commutes with scalar multiplication, every
-- eigenspace is stable under that action and can subsequently be decomposed
-- into irreducible sectors by the appropriate representation theory.

record EquivariantModeSystem : Set₁ where
  constructor equivariantModeSystem
  field
    State : Set
    Symmetry : Set
    act : Symmetry → State → State
    operator : State → State
    scale : Nat → State → State
    operatorCommutesWithAction :
      (g : Symmetry) → (x : State) →
      operator (act g x) ≡ act g (operator x)
    actionCommutesWithScale :
      (g : Symmetry) → (eigenvalue : Nat) → (x : State) →
      act g (scale eigenvalue x) ≡ scale eigenvalue (act g x)

open EquivariantModeSystem public

Eigenstate : (system : EquivariantModeSystem) → Nat → State system → Set
Eigenstate system eigenvalue x =
  operator system x ≡ scale system eigenvalue x

actionPreservesEigenstate :
  (system : EquivariantModeSystem) →
  (eigenvalue : Nat) →
  (g : Symmetry system) →
  (x : State system) →
  Eigenstate system eigenvalue x →
  Eigenstate system eigenvalue (act system g x)
actionPreservesEigenstate system eigenvalue g x eigen =
  trans
    (operatorCommutesWithAction system g x)
    (trans
      (cong (act system g) eigen)
      (actionCommutesWithScale system g eigenvalue x))

------------------------------------------------------------------------
-- A complete finite witness.

data ParityState : Set where
  evenState : ParityState
  oddState : ParityState

data Reflection : Set where
  identityReflection : Reflection
  polarityReflection : Reflection

parityAction : Reflection → ParityState → ParityState
parityAction identityReflection state = state
parityAction polarityReflection evenState = oddState
parityAction polarityReflection oddState = evenState

identityOperator : ParityState → ParityState
identityOperator state = state

identityScale : Nat → ParityState → ParityState
identityScale eigenvalue state = state

identityOperatorCommutes :
  (g : Reflection) → (x : ParityState) →
  identityOperator (parityAction g x)
  ≡ parityAction g (identityOperator x)
identityOperatorCommutes g x = refl

identityScaleCommutes :
  (g : Reflection) → (eigenvalue : Nat) → (x : ParityState) →
  parityAction g (identityScale eigenvalue x)
  ≡ identityScale eigenvalue (parityAction g x)
identityScaleCommutes g eigenvalue x = refl

canonicalEquivariantModeSystem : EquivariantModeSystem
canonicalEquivariantModeSystem =
  equivariantModeSystem
    ParityState
    Reflection
    parityAction
    identityOperator
    identityScale
    identityOperatorCommutes
    identityScaleCommutes

canonicalEvenEigenstate :
  Eigenstate canonicalEquivariantModeSystem 1 evenState
canonicalEvenEigenstate = refl

reflectedEvenRemainsEigenstate :
  Eigenstate canonicalEquivariantModeSystem 1
    (act canonicalEquivariantModeSystem polarityReflection evenState)
reflectedEvenRemainsEigenstate =
  actionPreservesEigenstate
    canonicalEquivariantModeSystem
    1
    polarityReflection
    evenState
    canonicalEvenEigenstate

------------------------------------------------------------------------
-- Application typing.  The same commuting-action theorem can be instantiated
-- in several lanes, but each lane keeps its own concrete operator, symmetry,
-- support, coefficients, and analytic estimates.

data ApplicationLane : Set where
  grokkingRepresentationLane : ApplicationLane
  neuralLaplacianLane : ApplicationLane
  reactionDiffusionLane : ApplicationLane
  navierStokesFourierLane : ApplicationLane
  yangMillsGaugeLane : ApplicationLane
  quantumExcitationLane : ApplicationLane

record EquivariantSectorBoundary : Set where
  constructor equivariantSectorBoundary
  field
    commutingOperatorSelectsUniqueExceptionalLattice : Bool
    commutingOperatorSelectsUniqueExceptionalLatticeIsFalse :
      commutingOperatorSelectsUniqueExceptionalLattice ≡ false

    genericSectorInterfaceSuppliesSharpNSOrYMCoefficients : Bool
    genericSectorInterfaceSuppliesSharpNSOrYMCoefficientsIsFalse :
      genericSectorInterfaceSuppliesSharpNSOrYMCoefficients ≡ false

    irrepLabelsAloneDeriveQuantumProbabilities : Bool
    irrepLabelsAloneDeriveQuantumProbabilitiesIsFalse :
      irrepLabelsAloneDeriveQuantumProbabilities ≡ false

    eigenspaceStabilityUnderCommutingActionIsReusable : Bool
    eigenspaceStabilityUnderCommutingActionIsReusableIsTrue :
      eigenspaceStabilityUnderCommutingAction ≡ true

open EquivariantSectorBoundary public

canonicalEquivariantSectorBoundary : EquivariantSectorBoundary
canonicalEquivariantSectorBoundary =
  equivariantSectorBoundary false refl false refl false refl true refl
