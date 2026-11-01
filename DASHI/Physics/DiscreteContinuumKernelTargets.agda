{-# OPTIONS --safe #-}
module DASHI.Physics.DiscreteContinuumKernelTargets where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Core.ReversibleDissipativeKernelSplit

------------------------------------------------------------------------
-- Exact theorem-facing interface for a discrete-to-continuum result.
-- The analytic meanings of limits, norms, and derivatives are supplied by the
-- selected analysis library rather than faked with finite booleans.

record DiscretisationFamily : Set₁ where
  field
    DiscreteState : Nat → Nat → Set
    ContinuumState : Set
    spatialStep : Nat → Nat
    temporalStep : Nat → Nat
    discreteKernel : ∀ h dt → DiscreteState h dt → DiscreteState h dt
    embed : ∀ {h dt} → DiscreteState h dt → ContinuumState
    continuumGenerator : ContinuumState → ContinuumState
open DiscretisationFamily public

record DiscreteContinuumTheorem
  (family : DiscretisationFamily) : Set₁ where
  field
    boundaryConditions : Set
    physicalUnitsMap : Set
    localConsistency : Set
    stabilityEstimate : Set
    compactnessOrCompleteness : Set
    generatorIdentification : Set
    convergence : Set
open DiscreteContinuumTheorem public

------------------------------------------------------------------------
-- First-order wave-system target.  The actual field, Laplacian, scalar
-- multiplication, and derivative theory are parameters.

record WaveSystemTarget : Set₁ where
  field
    Field : Set
    PhaseState : Set
    position : PhaseState → Field
    momentum : PhaseState → Field
    laplacian : Field → Field
    waveSpeedSquared : Set
    positionDerivativeEqualsMomentum : Set
    momentumDerivativeEqualsWaveOperator : Set
    energyControl : Set
    dispersionConvergence : Set
open WaveSystemTarget public

------------------------------------------------------------------------
-- MDL/action correspondence must be quantitative, not analogy.

record MDLActionAsymptoticTarget : Set₁ where
  field
    Configuration : Set
    resolution : Set
    mdl : resolution → Configuration → Nat
    action : Configuration → Set
    scaleFactor : resolution → Set
    offset : resolution → Set
    asymptoticComparison : Set
    minimiserConvergence : Set
    empiricalConstantMatching : Set
open MDLActionAsymptoticTarget public

------------------------------------------------------------------------
-- Metric and causal geometry selection.

record IntrinsicMetricSelectionTarget : Set₁ where
  field
    KernelCarrier : Set
    intrinsicKernelData : KernelCarrier
    dimensionDerived : Set
    signatureDerived : Set
    causalConeDerived : Set
    connectionDerived : Set
    curvatureDerived : Set
    sourceCouplingDerived : Set
    empiricalMetricMatch : Set
open IntrinsicMetricSelectionTarget public

record PhysicsDepthBoundary : Set where
  constructor physics-depth-boundary
  field
    discreteContinuumInterfacePresent : Bool
    discreteContinuumInterfacePresentIsTrue : discreteContinuumInterfacePresent ≡ true
    continuumConvergenceProvedGenerically : Bool
    continuumConvergenceProvedGenericallyIsFalse : continuumConvergenceProvedGenerically ≡ false
    valuationSelectsMetricAutomatically : Bool
    valuationSelectsMetricAutomaticallyIsFalse : valuationSelectsMetricAutomatically ≡ false
    mdlEqualsActionAutomatically : Bool
    mdlEqualsActionAutomaticallyIsFalse : mdlEqualsActionAutomatically ≡ false
    reversibleAndDissipativeOperatorsIdentified : Bool
    reversibleAndDissipativeOperatorsIdentifiedIsFalse :
      reversibleAndDissipativeOperatorsIdentified ≡ false
open PhysicsDepthBoundary public

canonicalPhysicsDepthBoundary : PhysicsDepthBoundary
canonicalPhysicsDepthBoundary =
  physics-depth-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
