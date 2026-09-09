module DASHI.ComputerScience.QuantumExecutionFibreAdapterExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.DASHIQuantumBridge as Bridge
import DASHI.Algebra.Quantum.DASHIHybridExecution as Hybrid

------------------------------------------------------------------------
-- QUANTUM EXECUTION AS A PEER FIBRE
--
-- This adapter does not encode the classical register machine into a quantum
-- radix.  Quantum execution keeps its own state carrier, reversible circuits,
-- Fourier transform, measurement/sample and successful-recovery obligations.
-- The shared layer is only the consumer-indexed complexity interface.
------------------------------------------------------------------------

record QuantumCostProfile : Set where
  constructor quantumCostProfile
  field
    basisDimension : Nat
    logicalRegisterCount : Nat
    reversibleCircuitCount : Nat
    fourierTransformCount : Nat
    oracleInvocationCount : Nat
    measurementSampleCount : Nat
    recoveryStepCount : Nat
    gateCount : Nat
    circuitDepth : Nat

open QuantumCostProfile public

record QuantumCostConsumer : Set₁ where
  constructor quantumCostConsumer
  field
    Outcome : Set
    observeQuantumCost : QuantumCostProfile → Outcome

open QuantumCostConsumer public

gateCountConsumer : QuantumCostConsumer
gateCountConsumer = quantumCostConsumer Nat gateCount

depthConsumer : QuantumCostConsumer
depthConsumer = quantumCostConsumer Nat circuitDepth

basisDimensionConsumer : QuantumCostConsumer
basisDimensionConsumer = quantumCostConsumer Nat basisDimension

KQ :
  (consumer : QuantumCostConsumer) →
  QuantumCostProfile →
  QuantumCostConsumer.Outcome consumer
KQ consumer profile = observeQuantumCost consumer profile

------------------------------------------------------------------------
-- Finite quantum-register execution path.
------------------------------------------------------------------------

record FiniteQuantumExecutionFibre : Set₂ where
  constructor finiteQuantumExecutionFibre
  field
    basis : Finite.FiniteBasis
    register : Finite.FiniteQuantumRegister basis
    circuit : Finite.ReversibleCircuit register
    fourier : QFT.FiniteFourierTransform register

    inputBasis : Finite.Basis basis
    preparedState : Finite.State register
    preparationExact : preparedState ≡ Finite.prepare register inputBasis

    transportedState : Finite.State register
    transportExact : transportedState ≡ Finite.run circuit preparedState

    observedBasis : Finite.Basis basis
    observationExact : observedBasis ≡ Finite.observe register transportedState

    cost : QuantumCostProfile

open FiniteQuantumExecutionFibre public

quantumTwoStatePath :
  (F : FiniteQuantumExecutionFibre) →
  Complexity.ExecutionFibrePath (Finite.State (register F))
quantumTwoStatePath F =
  Complexity.executionFibrePath
    (preparedState F ∷ transportedState F ∷ [])

quantumCircuitTransitionCount :
  (F : FiniteQuantumExecutionFibre) →
  Complexity.pathTransitionCount (quantumTwoStatePath F) ≡ 1
quantumCircuitTransitionCount F = refl

------------------------------------------------------------------------
-- Existing Shor period-finding surface as an algorithmic quantum fibre.
------------------------------------------------------------------------

record ShorExecutionFibre
    (H : Shor.HiddenPeriodProblem) : Set₂ where
  constructor shorExecutionFibre
  field
    machine : Shor.ShorPeriodFindingMachine H
    seed : Nat
    sample : Shor.PeriodSample machine
    sampleExact : sample ≡ Shor.periodExecute machine seed
    successful : Shor.periodSuccessful machine sample
    recovered : Nat
    recoveredExact : recovered ≡ Shor.recoverPeriod machine sample
    recoveredPeriodExact : recovered ≡ Shor.period H
    cost : QuantumCostProfile

open ShorExecutionFibre public

------------------------------------------------------------------------
-- Existing DASHI hybrid quantum bridge.
------------------------------------------------------------------------

record HybridQuantumExecutionFibre : Set₂ where
  constructor hybridQuantumExecutionFibre
  field
    descent : Bridge.StrictDescentSystem
    bridge : Bridge.CertifiedQuantumBridge descent
    hybrid : Hybrid.HybridExecution descent bridge
    input : Bridge.State descent
    quantumObserved : Bridge.State descent
    observedExact : quantumObserved ≡ Hybrid.hybridStep descent bridge hybrid input
    semanticStepExact : quantumObserved ≡ Bridge.step descent input
    cost : QuantumCostProfile

open HybridQuantumExecutionFibre public

------------------------------------------------------------------------
-- Boundary: shared result/consumer surface does not collapse execution models.
------------------------------------------------------------------------

record QuantumExecutionFibreBoundary : Set where
  constructor quantumExecutionFibreBoundary
  field
    quantumIsClassicalRadixEncoding : Bool
    reversibleCircuitIsClassicalInstructionTrace : Bool
    sameRecoveredArithmeticResultImpliesSameExecutionPath : Bool
    quantumAndClassicalMayShareCostVocabulary : Bool
    gateCountEqualsClassicalTransitionCountByDefinition : Bool
    measurementCostSeparate : Bool
    successEvidenceRequiredForShorRecovery : Bool

canonicalQuantumExecutionFibreBoundary : QuantumExecutionFibreBoundary
canonicalQuantumExecutionFibreBoundary =
  quantumExecutionFibreBoundary
    false false false true false true true
