module DASHI.Promotion.FiniteTernaryQuantumCircuitAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Core.OperatorTypes using (Invertible)
open import DASHI.Algebra.Quantum.TernaryCircuit
open import DASHI.Algebra.Quantum.QutritUnitaryBridge
import DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter as Binary

------------------------------------------------------------------------
-- A finite qutrit/permutation adapter adjacent to the existing two-state
-- Schrodinger/Born toy.  This records single- and two-qutrit reversible basis
-- gates without promoting amplitudes, arbitrary unitaries, or algorithms.

record FiniteTernaryQuantumCircuitAdapter : Set₁ where
  field
    upstreamBinaryToy :
      Binary.FiniteQuantumSchrodingerBornAdapter

    qutritBasisStates : List QutritBasis
    singleQutritPermutationSemantics :
      FiniteQutritPermutationSemantics
    twoQutritPermutationSemantics :
      FiniteQutritPermutationSemantics

    cycleOrderThree :
      ∀ q →
      cycleQutrit (cycleQutrit (cycleQutrit q)) ≡ q

    cycleIsInvertible : Invertible cycleQutrit

    controlledCycleIsReversible :
      ∀ pair →
      inverseControlledCycle (controlledCycle pair) ≡ pair

    abstractUnitaryBridgeReady : Bool
    abstractUnitaryBridgeReadyIsTrue :
      abstractUnitaryBridgeReady ≡ true

    finiteBasisPermutationOnly : Bool
    finiteBasisPermutationOnlyIsTrue :
      finiteBasisPermutationOnly ≡ true

    amplitudeSuperpositionSupplied : Bool
    amplitudeSuperpositionSuppliedIsFalse :
      amplitudeSuperpositionSupplied ≡ false

    arbitraryUnitaryMatricesSupplied : Bool
    arbitraryUnitaryMatricesSuppliedIsFalse :
      arbitraryUnitaryMatricesSupplied ≡ false

    quantumAlgorithmLibrarySupplied : Bool
    quantumAlgorithmLibrarySuppliedIsFalse :
      quantumAlgorithmLibrarySupplied ≡ false

    fullQutritQuantumComputerPromoted : Bool
    fullQutritQuantumComputerPromotedIsFalse :
      fullQutritQuantumComputerPromoted ≡ false

open FiniteTernaryQuantumCircuitAdapter public

canonicalFiniteTernaryQuantumCircuitAdapter :
  FiniteTernaryQuantumCircuitAdapter
canonicalFiniteTernaryQuantumCircuitAdapter =
  record
    { upstreamBinaryToy =
        Binary.canonicalFiniteQuantumSchrodingerBornAdapter
    ; qutritBasisStates = qNeg ∷ qZero ∷ qPos ∷ []
    ; singleQutritPermutationSemantics =
        canonicalFiniteQutritPermutationSemantics
    ; twoQutritPermutationSemantics =
        canonicalFiniteQutritPairPermutationSemantics
    ; cycleOrderThree = cycle³
    ; cycleIsInvertible = cycleQutritInvertible
    ; controlledCycleIsReversible = controlledCycleInverseLeft
    ; abstractUnitaryBridgeReady = true
    ; abstractUnitaryBridgeReadyIsTrue = refl
    ; finiteBasisPermutationOnly = true
    ; finiteBasisPermutationOnlyIsTrue = refl
    ; amplitudeSuperpositionSupplied = false
    ; amplitudeSuperpositionSuppliedIsFalse = refl
    ; arbitraryUnitaryMatricesSupplied = false
    ; arbitraryUnitaryMatricesSuppliedIsFalse = refl
    ; quantumAlgorithmLibrarySupplied = false
    ; quantumAlgorithmLibrarySuppliedIsFalse = refl
    ; fullQutritQuantumComputerPromoted = false
    ; fullQutritQuantumComputerPromotedIsFalse = refl
    }
