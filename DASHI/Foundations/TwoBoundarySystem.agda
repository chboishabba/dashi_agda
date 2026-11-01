module DASHI.Foundations.TwoBoundarySystem where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Generic two-boundary architecture
--
-- This module isolates the structural content shared by boundary-value
-- problems, pre/post-selected quantum ensembles, and non-quantum diachronic
-- models.  It deliberately makes no claim that every instance is quantum or
-- retrocausal.
------------------------------------------------------------------------

record TwoBoundarySystem : Set₁ where
  field
    State           : Set
    InitialBoundary : Set
    FinalBoundary   : Set

    compatible :
      InitialBoundary →
      FinalBoundary →
      State →
      Set

record BoundaryWitness
  (S : TwoBoundarySystem)
  (initial : TwoBoundarySystem.InitialBoundary S)
  (final   : TwoBoundarySystem.FinalBoundary S)
  (state   : TwoBoundarySystem.State S) : Set where
  constructor witnessed
  field
    proof : TwoBoundarySystem.compatible S initial final state

------------------------------------------------------------------------
-- Boundary propagation
------------------------------------------------------------------------

record TwoBoundaryPropagation (S : TwoBoundarySystem) : Set₁ where
  field
    forwardFrom :
      TwoBoundarySystem.InitialBoundary S →
      TwoBoundarySystem.State S

    backwardFrom :
      TwoBoundarySystem.FinalBoundary S →
      TwoBoundarySystem.State S

-- The two oriented legs are retained as a pair.  They are not collapsed into
-- one state merely because both constrain the same intermediate observation.
record Junction (S : TwoBoundarySystem) : Set where
  constructor junction
  field
    forwardLeg  : TwoBoundarySystem.State S
    backwardLeg : TwoBoundarySystem.State S

buildJunction :
  {S : TwoBoundarySystem} →
  TwoBoundaryPropagation S →
  TwoBoundarySystem.InitialBoundary S →
  TwoBoundarySystem.FinalBoundary S →
  Junction S
buildJunction P initial final =
  junction
    (TwoBoundaryPropagation.forwardFrom P initial)
    (TwoBoundaryPropagation.backwardFrom P final)

------------------------------------------------------------------------
-- Conditional observation kernel and region of admissibility
------------------------------------------------------------------------

record TwoBoundaryKernel (S : TwoBoundarySystem) : Set₁ where
  field
    Measurement : Set
    Outcome     : Measurement → Set
    Weight      : Set
    Positive    : Weight → Set

    outcomeWeight :
      (initial : TwoBoundarySystem.InitialBoundary S) →
      (final   : TwoBoundarySystem.FinalBoundary S) →
      (measurement : Measurement) →
      Outcome measurement →
      Weight

    totalWeight :
      TwoBoundarySystem.InitialBoundary S →
      TwoBoundarySystem.FinalBoundary S →
      Measurement →
      Weight

record InRegionOfConvergence
  {S : TwoBoundarySystem}
  (K : TwoBoundaryKernel S)
  (initial : TwoBoundarySystem.InitialBoundary S)
  (final   : TwoBoundarySystem.FinalBoundary S)
  (measurement : TwoBoundaryKernel.Measurement K) : Set where
  constructor convergent
  field
    totalPositive :
      TwoBoundaryKernel.Positive K
        (TwoBoundaryKernel.totalWeight K initial final measurement)

------------------------------------------------------------------------
-- Marginal recovery
--
-- A two-boundary theory should state explicitly how ordinary one-boundary
-- prediction or retrodiction is recovered when the opposite boundary is
-- forgotten/summed over.  The actual summation law belongs to each instance.
------------------------------------------------------------------------

record MarginalRecovery
  (S : TwoBoundarySystem)
  (K : TwoBoundaryKernel S) : Set₁ where
  field
    Prediction : Set
    Retrodiction : Set

    forgetFinal :
      TwoBoundarySystem.InitialBoundary S →
      TwoBoundaryKernel.Measurement K →
      Prediction

    forgetInitial :
      TwoBoundarySystem.FinalBoundary S →
      TwoBoundaryKernel.Measurement K →
      Retrodiction

------------------------------------------------------------------------
-- Boundary reversal versus causal interpretation
------------------------------------------------------------------------

record BoundaryFold (S : TwoBoundarySystem) : Set₁ where
  field
    reverseState :
      TwoBoundarySystem.State S →
      TwoBoundarySystem.State S

    initialToFinal :
      TwoBoundarySystem.InitialBoundary S →
      TwoBoundarySystem.FinalBoundary S

    finalToInitial :
      TwoBoundarySystem.FinalBoundary S →
      TwoBoundarySystem.InitialBoundary S

    reverseState-involutive :
      (x : TwoBoundarySystem.State S) →
      reverseState (reverseState x) ≡ x

    initial-roundtrip :
      (x : TwoBoundarySystem.InitialBoundary S) →
      finalToInitial (initialToFinal x) ≡ x

    final-roundtrip :
      (x : TwoBoundarySystem.FinalBoundary S) →
      initialToFinal (finalToInitial x) ≡ x

-- Presence of BoundaryFold proves a reversible structural correspondence.  It
-- does not by itself prove controllable signalling into the past or an
-- ontological future-to-past causal mechanism.
