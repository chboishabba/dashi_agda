module DASHI.Core.FibrePreservingDynamicsExact where

------------------------------------------------------------------------
-- Dynamics and symmetries internal to a projected fibre.
--
-- This module sits on top of FibreRestrictionCore.  It does not introduce a
-- second quotient abstraction.  It classifies operators on the hidden carrier
-- according to whether their action is visible after projection.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.FibreRestrictionCore as Fibre

CarrierOperator : (core : Fibre.FibreRestrictionCore) → Set
CarrierOperator core = Fibre.Carrier core → Fibre.Carrier core

SurfaceInvariant :
  (core : Fibre.FibreRestrictionCore) →
  CarrierOperator core → Set
SurfaceInvariant core operator =
  ∀ x → Fibre.project core (operator x) ≡ Fibre.project core x

record FibreEndomorphism
    (core : Fibre.FibreRestrictionCore) : Set where
  constructor fibreEndomorphism
  field
    operator : CarrierOperator core
    preservesSurface : SurfaceInvariant core operator

open FibreEndomorphism public

identityFibreEndomorphism :
  (core : Fibre.FibreRestrictionCore) → FibreEndomorphism core
identityFibreEndomorphism core =
  fibreEndomorphism (λ x → x) (λ x → refl)

composeFibreEndomorphism :
  ∀ {core : Fibre.FibreRestrictionCore} →
  FibreEndomorphism core →
  FibreEndomorphism core →
  FibreEndomorphism core
composeFibreEndomorphism {core} first second =
  fibreEndomorphism
    (λ x → operator first (operator second x))
    (λ x →
      trans
        (preservesSurface first (operator second x))
        (preservesSurface second x))

record HiddenTransition
    (core : Fibre.FibreRestrictionCore)
    (operator : CarrierOperator core)
    (x : Fibre.Carrier core) : Set where
  constructor hiddenTransition
  field
    fineStateChanges : operator x ≡ x → ⊥
    coarseSurfaceStable :
      Fibre.project core (operator x) ≡ Fibre.project core x

open HiddenTransition public

fibreEndomorphismHiddenWhenNontrivial :
  ∀ {core : Fibre.FibreRestrictionCore}
    (endomorphism : FibreEndomorphism core)
    (x : Fibre.Carrier core) →
  operator endomorphism x ≡ x → ⊥ →
  HiddenTransition core (operator endomorphism) x
fibreEndomorphismHiddenWhenNontrivial endomorphism x changes =
  hiddenTransition changes (preservesSurface endomorphism x)

hiddenTransitionWitnessesProjectionNoninjective :
  ∀ {core : Fibre.FibreRestrictionCore}
    {operator : CarrierOperator core}
    {x : Fibre.Carrier core} →
  HiddenTransition core operator x →
  ((a b : Fibre.Carrier core) →
    Fibre.project core a ≡ Fibre.project core b → a ≡ b) →
  ⊥
hiddenTransitionWitnessesProjectionNoninjective hidden injective =
  fineStateChanges hidden
    (injective
      _ _
      (coarseSurfaceStable hidden))

------------------------------------------------------------------------
-- Fibre automorphisms / deck-style symmetries.
------------------------------------------------------------------------

record FibreAutomorphism
    (core : Fibre.FibreRestrictionCore) : Set where
  constructor fibreAutomorphism
  field
    forward backward : CarrierOperator core
    forwardPreservesSurface : SurfaceInvariant core forward
    backwardPreservesSurface : SurfaceInvariant core backward
    backwardAfterForward : (x : Fibre.Carrier core) → backward (forward x) ≡ x
    forwardAfterBackward : (x : Fibre.Carrier core) → forward (backward x) ≡ x

open FibreAutomorphism public

fibreAutomorphismAsEndomorphism :
  ∀ {core : Fibre.FibreRestrictionCore} →
  FibreAutomorphism core → FibreEndomorphism core
fibreAutomorphismAsEndomorphism automorphism =
  fibreEndomorphism
    (forward automorphism)
    (forwardPreservesSurface automorphism)

record NontrivialFibreAutomorphism
    (core : Fibre.FibreRestrictionCore) : Set where
  constructor nontrivialFibreAutomorphism
  field
    automorphism : FibreAutomorphism core
    movedPoint : Fibre.Carrier core
    movedPointActuallyMoves :
      forward automorphism movedPoint ≡ movedPoint → ⊥

open NontrivialFibreAutomorphism public

nontrivialFibreAutomorphismCreatesHiddenTransition :
  ∀ {core : Fibre.FibreRestrictionCore} →
  (symmetry : NontrivialFibreAutomorphism core) →
  HiddenTransition
    core
    (forward (automorphism symmetry))
    (movedPoint symmetry)
nontrivialFibreAutomorphismCreatesHiddenTransition symmetry =
  hiddenTransition
    (movedPointActuallyMoves symmetry)
    (forwardPreservesSurface
      (automorphism symmetry)
      (movedPoint symmetry))

nontrivialFibreAutomorphismBlocksProjectionInjectivity :
  ∀ {core : Fibre.FibreRestrictionCore} →
  NontrivialFibreAutomorphism core →
  ((a b : Fibre.Carrier core) →
    Fibre.project core a ≡ Fibre.project core b → a ≡ b) →
  ⊥
nontrivialFibreAutomorphismBlocksProjectionInjectivity symmetry =
  hiddenTransitionWitnessesProjectionNoninjective
    (nontrivialFibreAutomorphismCreatesHiddenTransition symmetry)

------------------------------------------------------------------------
-- Descent to an explicit surface operator is stronger than mere hidden motion.
------------------------------------------------------------------------

record DescendsToSurface
    (core : Fibre.FibreRestrictionCore)
    (carrierOperator : CarrierOperator core) : Set₁ where
  constructor descendsToSurface
  field
    surfaceOperator : Fibre.Surface core → Fibre.Surface core
    commutesWithProjection :
      (x : Fibre.Carrier core) →
      Fibre.project core (carrierOperator x)
      ≡ surfaceOperator (Fibre.project core x)

open DescendsToSurface public

surfaceInvariantDescendsAsIdentity :
  ∀ {core : Fibre.FibreRestrictionCore}
    {carrierOperator : CarrierOperator core} →
  SurfaceInvariant core carrierOperator →
  DescendsToSurface core carrierOperator
surfaceInvariantDescendsAsIdentity invariant =
  descendsToSurface (λ surface → surface) invariant

record FibrePreservingDynamicsBoundary : Set where
  constructor fibrePreservingDynamicsBoundary
  field
    hiddenFineMotionCanExistAtFixedSurface : Bool
    hiddenFineMotionCanExistAtFixedSurfaceIsTrue :
      hiddenFineMotionCanExistAtFixedSurface ≡ true
    nontrivialFibreSymmetryForcesProjectionLoss : Bool
    nontrivialFibreSymmetryForcesProjectionLossIsTrue :
      nontrivialFibreSymmetryForcesProjectionLoss ≡ true
    surfaceStabilityImpliesFineStateIdentity : Bool
    surfaceStabilityImpliesFineStateIdentityIsFalse :
      surfaceStabilityImpliesFineStateIdentity ≡ false

canonicalFibrePreservingDynamicsBoundary : FibrePreservingDynamicsBoundary
canonicalFibrePreservingDynamicsBoundary =
  fibrePreservingDynamicsBoundary true refl true refl false refl
