module DASHI.Physics.Closure.MonsterC3UniformCountingEnsembleExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Physics.Closure.MonsterC3EntropyStateCountingExact as StateCount
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo

------------------------------------------------------------------------
-- Exact normalized FINITE COUNTING ensemble over the already-paid cardinalities.
--
-- This pays a mathematical probability layer only:
--
--   fine  : Fin 196883, each state weight 1/196883
--   coarse: Fin 53,     each state weight 1/53
--
-- It deliberately does NOT identify those Fin carriers with literal Monster
-- module states, does not assert equiprobability in a physical ensemble, and
-- does not turn counting entropy into thermodynamic/von-Neumann entropy.
------------------------------------------------------------------------

record UniformProbability : Set where
  constructor uniformProbability
  field
    numerator : Nat
    denominator : Nat

open UniformProbability public

fineUniformWeight : UniformProbability
fineUniformWeight = uniformProbability 1 196883

coarseUniformWeight : UniformProbability
coarseUniformWeight = uniformProbability 1 53

record UniformNormalization : Set where
  constructor uniformNormalization
  field
    stateCount : Nat
    weightNumerator : Nat
    weightDenominator : Nat
    normalizationArithmetic :
      weightNumerator * stateCount ≡ weightDenominator

open UniformNormalization public

fineUniformNormalization : UniformNormalization
fineUniformNormalization =
  uniformNormalization 196883 1 196883 refl

coarseUniformNormalization : UniformNormalization
coarseUniformNormalization =
  uniformNormalization 53 1 53 refl

------------------------------------------------------------------------
-- Generic statistical-ensemble adapters.
--
-- Unit-valued energy/observable slots are explicit placeholders.  They satisfy
-- the interface shape but carry no physical Hamiltonian or thermodynamic claim.
------------------------------------------------------------------------

data FineMacrostate : Set where
  completeFineCarrier : FineMacrostate

data CoarseMacrostate : Set where
  residualVisibleCarrier : CoarseMacrostate

fineCountingEnsemble : Thermo.StatisticalEnsemble
fineCountingEnsemble = record
  { Microstate = Fin 196883
  ; Macrostate = FineMacrostate
  ; Probability = UniformProbability
  ; Energy = ⊤
  ; Parameter = ⊤
  ; PartitionValue = Nat
  ; Observable = ⊤
  ; Expectation = ⊤
  ; macrostate = λ _ → completeFineCarrier
  ; probability = λ _ _ → fineUniformWeight
  ; microEnergy = λ _ → tt
  ; partitionFunction = λ _ → 196883
  ; expectation = λ _ _ → tt
  ; Normalised = λ _ →
      weightNumerator fineUniformNormalization
      * stateCount fineUniformNormalization
      ≡ weightDenominator fineUniformNormalization
  ; EnsembleAdmissible = λ _ → ⊤
  }

coarseCountingEnsemble : Thermo.StatisticalEnsemble
coarseCountingEnsemble = record
  { Microstate = Fin 53
  ; Macrostate = CoarseMacrostate
  ; Probability = UniformProbability
  ; Energy = ⊤
  ; Parameter = ⊤
  ; PartitionValue = Nat
  ; Observable = ⊤
  ; Expectation = ⊤
  ; macrostate = λ _ → residualVisibleCarrier
  ; probability = λ _ _ → coarseUniformWeight
  ; microEnergy = λ _ → tt
  ; partitionFunction = λ _ → 53
  ; expectation = λ _ _ → tt
  ; Normalised = λ _ →
      weightNumerator coarseUniformNormalization
      * stateCount coarseUniformNormalization
      ≡ weightDenominator coarseUniformNormalization
  ; EnsembleAdmissible = λ _ → ⊤
  }

fineNormalisedWitness :
  Thermo.StatisticalEnsemble.Normalised fineCountingEnsemble tt
fineNormalisedWitness = refl

coarseNormalisedWitness :
  Thermo.StatisticalEnsemble.Normalised coarseCountingEnsemble tt
coarseNormalisedWitness = refl

------------------------------------------------------------------------
-- Cross-owner count agreement.
------------------------------------------------------------------------

fineCountAgreesWithMonsterReceipt :
  stateCount fineUniformNormalization
  ≡ StateCount.MonsterC3StateCountingReceipt.identityVisibleStates
      StateCount.canonicalMonsterC3StateCountingReceipt
fineCountAgreesWithMonsterReceipt = refl

coarseCountAgreesWithMonsterReceipt :
  stateCount coarseUniformNormalization
  ≡ StateCount.MonsterC3StateCountingReceipt.nontrivialPhaseVisibleStates
      StateCount.canonicalMonsterC3StateCountingReceipt
coarseCountAgreesWithMonsterReceipt = refl

record CountingEnsembleBoundary : Set where
  constructor countingEnsembleBoundary
  field
    normalizedFiniteCountingWeightsPaid : Bool
    normalizedFiniteCountingWeightsPaidIsTrue :
      normalizedFiniteCountingWeightsPaid ≡ true

    statisticalEnsembleInterfaceInstantiated : Bool
    statisticalEnsembleInterfaceInstantiatedIsTrue :
      statisticalEnsembleInterfaceInstantiated ≡ true

    finCarrierIdentifiedWithLiteralMonsterStates : Bool
    finCarrierIdentifiedWithLiteralMonsterStatesIsFalse :
      finCarrierIdentifiedWithLiteralMonsterStates ≡ false

    uniformCountingMeasureIsPhysicalThermalEnsemble : Bool
    uniformCountingMeasureIsPhysicalThermalEnsembleIsFalse :
      uniformCountingMeasureIsPhysicalThermalEnsemble ≡ false

    unitEnergyPlaceholderIsPhysicalHamiltonian : Bool
    unitEnergyPlaceholderIsPhysicalHamiltonianIsFalse :
      unitEnergyPlaceholderIsPhysicalHamiltonian ≡ false

    countingNormalizationDefinesThermodynamicEntropy : Bool
    countingNormalizationDefinesThermodynamicEntropyIsFalse :
      countingNormalizationDefinesThermodynamicEntropy ≡ false

    countingNormalizationDefinesVonNeumannEntropy : Bool
    countingNormalizationDefinesVonNeumannEntropyIsFalse :
      countingNormalizationDefinesVonNeumannEntropy ≡ false

    countingNormalizationCreatesGravity : Bool
    countingNormalizationCreatesGravityIsFalse :
      countingNormalizationCreatesGravity ≡ false

open CountingEnsembleBoundary public

canonicalCountingEnsembleBoundary : CountingEnsembleBoundary
canonicalCountingEnsembleBoundary =
  countingEnsembleBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
