module DASHI.Physics.ThreeBody.PredictiveBoundary where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.Closure.Basin
open import DASHI.Physics.ThreeBody.Step
open import DASHI.Physics.ThreeBody.Regime
open import DASHI.Physics.ThreeBody.Energy
open import DASHI.Physics.ThreeBody.Wave

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

------------------------------------------------------------------------
-- Delta-side scaffold for the three-body cluster.
--
-- This is theorem-thin by design. It defines local model surfaces and
-- placeholder obligations without claiming global prediction/chaos proofs.

record Delta3Body
  (State : Set)
  : Set₁ where
  field
    DeltaState : Set
    encodeDelta : State → DeltaState
    deltaStep : DeltaState → DeltaState

open Delta3Body public

record EnergyΔ3
  (State : Set)
  : Set₁ where
  field
    deltaSurface : Delta3Body State
    QuadraticCarrier : Set
    transportΔ3 : DeltaState deltaSurface → QuadraticCarrier
    canonicalQuadratic3 : QuadraticCarrier → Nat
    energyΔ3 : State → Nat
    energyΔ3-def :
      ∀ s →
        energyΔ3 s
        ≡
        canonicalQuadratic3
          (transportΔ3 (encodeDelta deltaSurface s))

open EnergyΔ3 public

record Action3
  (State : Set)
  : Set₁ where
  field
    energySurface : EnergyΔ3 State
    action3 : (Nat → State) → Nat
    localWindowAction3 : Nat → (Nat → State) → Nat
    actionFromEnergySurface : Set

open Action3 public

record LocalPredictiveHorizon
  (State : Set)
  : Set₁ where
  field
    basinSurface : Basin State
    horizonDepth : Nat
    forecast : State → Nat → State
    localReconstruction : State → Set
    boundedForecast :
      ∀ (s : State) (n : Nat) →
        n ≤ horizonDepth →
        Set
    boundedForecastDepthOnly : Set
    noGlobalPredictionClaim : Set
    basinForecastCompatibility :
      ∀ s →
        Basin.InBasin basinSurface s →
        localReconstruction s

open LocalPredictiveHorizon public

record ChaosBoundary
  (State : Set)
  : Set₁ where
  field
    boundaryPredicate : State → Set
    boundaryCrossing : (Nat → State) → Set
    sensitiveNearBoundary : State → Set
    boundedLocalReconstructionNearBoundary : State → Set
    chaosBoundaryIsLocalSurface : Set
    noGlobalChaosClassificationClaim : Set

open ChaosBoundary public

record ThreeBodyPredictiveBoundaryLayer
  (State : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    stepSurface : ThreeBodyStep State
    regimeClassifier : ThreeBodyRegimeClassifier State
    energyActionSurface : ThreeBodyEnergyAction State Energy
    waveKernelSurface : ThreeBodyWaveKernel State Energy Phase
    delta3Surface : Delta3Body State
    energyΔ3Surface : EnergyΔ3 State
    action3Surface : Action3 State
    predictiveHorizonSurface : LocalPredictiveHorizon State
    chaosBoundarySurface : ChaosBoundary State

    delta3LayerDefined : Set
    energyΔ3LayerDefined : Set
    action3LayerDefined : Set
    localPredictiveHorizonLayerDefined : Set
    chaosBoundaryLayerDefined : Set

    localReconstructionWithinHorizon : Set
    basinAnchoredPredictionSurface : Basin State
    boundaryOfContractionTheoremSurface : Set
    boundedForecastDepthCorollary : Set

open ThreeBodyPredictiveBoundaryLayer public
