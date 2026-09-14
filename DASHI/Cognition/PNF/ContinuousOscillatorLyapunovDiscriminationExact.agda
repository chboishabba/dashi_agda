module DASHI.Cognition.PNF.ContinuousOscillatorLyapunovDiscriminationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.ContinuousOscillatorUpdateLawAttributionExact as Update
import DASHI.Cognition.PNF.ContinuousOscillatorUpdateLawComparisonReceipt as Comparison

------------------------------------------------------------------------
-- ABSTRACT DISCRETE DESCENT CERTIFICATE
--
-- This owner intentionally does NOT identify a finite sampled decrease with a
-- global Lyapunov theorem.  A genuine global certificate must supply an energy
-- preorder and prove one-step nonincrease for every state in the declared
-- carrier.  Strict decrease, convergence, asymptotic stability, and semantic
-- truth are separate downstream obligations.
------------------------------------------------------------------------

record DiscreteDescentSystem : Set₁ where
  constructor discrete-descent-system
  field
    State : Set
    Energy : Set
    step : State → State
    energy : State → Energy
    _≤E_ : Energy → Energy → Set
    preorderReflexive : (e : Energy) → e ≤E e
    oneStepNonincrease : (s : State) → energy (step s) ≤E energy s
    stateCarrierReference : String
    energyReference : String
    updateReference : String
open DiscreteDescentSystem public

record StrictDescentOutsideInvariant
    (system : DiscreteDescentSystem) : Set₁ where
  constructor strict-descent-outside-invariant
  field
    Invariant : State system → Set
    _<E_ : Energy system → Energy system → Set
    strictOutside :
      (s : State system) →
      (Invariant s → ⊥) →
      energy system (step system s) <E energy system s
    invariantReference : String
open StrictDescentOutsideInvariant public

record ConvergencePayment
    (system : DiscreteDescentSystem) : Set₁ where
  constructor convergence-payment
  field
    LimitObject : Set
    convergesTo : State system → LimitObject → Set
    convergenceWitness : (s : State system) → Set
    convergenceReference : String
open ConvergencePayment public

------------------------------------------------------------------------
-- Candidate update-law ancestry retained.
------------------------------------------------------------------------

currentGradientCandidate : Update.OscillatorUpdateLawCandidate
currentGradientCandidate = Update.currentGradientCandidate

hebbianCandidate : Update.OscillatorUpdateLawCandidate
hebbianCandidate = Update.hebbianCandidate

ojaCandidate : Update.OscillatorUpdateLawCandidate
ojaCandidate = Update.ojaCandidate

kuramotoCandidate : Update.OscillatorUpdateLawCandidate
kuramotoCandidate = Update.kuramotoCandidate

comparisonReceipt : Comparison.ContinuousOscillatorUpdateLawComparisonReceipt
comparisonReceipt = Comparison.canonicalContinuousOscillatorUpdateLawComparisonReceipt

------------------------------------------------------------------------
-- Numerical receipt boundary.
------------------------------------------------------------------------

record SampledDescentReceiptBoundary : Set where
  constructor sampled-descent-receipt-boundary
  field
    finiteSeedNonincreaseCreatesGlobalTheorem : Bool
    finiteStepNonincreaseCreatesAllTimeTheorem : Bool
    commonDiagnosticEnergyIsNativeLyapunovForEveryCandidate : Bool
    monotoneWaveformMSECreatesSemanticTruth : Bool
    monotoneWaveformMSECreatesEmpiricalAdequacy : Bool
    sampledDescentCreatesMechanismIdentity : Bool
    sampledIncreaseRefutesEveryPossibleCandidateLyapunov : Bool
    numericalReceiptMayMotivateFormalSearch : Bool
open SampledDescentReceiptBoundary public

canonicalSampledDescentReceiptBoundary : SampledDescentReceiptBoundary
canonicalSampledDescentReceiptBoundary =
  sampled-descent-receipt-boundary
    false false false false false false false true

------------------------------------------------------------------------
-- WrongType / stability firewall.
------------------------------------------------------------------------

record ContinuousOscillatorLyapunovBoundary : Set where
  constructor continuous-oscillator-lyapunov-boundary
  field
    objectiveValueEqualsLyapunovFunctionByDefinition : Bool
    oneStepNonincreaseEqualsStrictDescent : Bool
    strictDescentEqualsConvergence : Bool
    convergenceEqualsAsymptoticStability : Bool
    dynamicalStabilityEqualsMemorySemanticCorrectness : Bool
    phaseCoherenceEqualsLowEnergy : Bool
    lowerEnergyEqualsTruth : Bool
    threeOscillatorsMoreStableByDefinition : Bool
    sixOscillatorsMoreStableByDefinition : Bool
    nineOscillatorsMoreStableByDefinition : Bool
    updateLawSourceBoundaryRetained : Bool
    comparisonBoundaryRetained : Bool
open ContinuousOscillatorLyapunovBoundary public

canonicalContinuousOscillatorLyapunovBoundary :
  ContinuousOscillatorLyapunovBoundary
canonicalContinuousOscillatorLyapunovBoundary =
  continuous-oscillator-lyapunov-boundary
    false false false false false false false false false false true true
