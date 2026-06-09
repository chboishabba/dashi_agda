module DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.QuantumQFTObligations as Quantum

------------------------------------------------------------------------
-- A deliberately finite two-state adapter.
--
-- This module inhabits a toy Schrodinger/Born surface: two basis states,
-- the identity time evolution, a symbolic zero Hamiltonian, and basis
-- projection probabilities.  The canonical receipt links back to the
-- quantum promotion obligation index, but it does not discharge the full
-- Hilbert/domain/Stone/Born/QFT obligations recorded there.

data TwoState : Set where
  ket0 : TwoState
  ket1 : TwoState

data BasisProjection : Set where
  projectKet0 : BasisProjection
  projectKet1 : BasisProjection

data FiniteAmplitude : Set where
  amp0 : FiniteAmplitude
  amp1 : FiniteAmplitude

data FiniteVector : Set where
  zeroVector : FiniteVector
  basis0Vector : FiniteVector
  basis1Vector : FiniteVector

stateVector : TwoState → FiniteVector
stateVector ket0 = basis0Vector
stateVector ket1 = basis1Vector

------------------------------------------------------------------------
-- Nat-coded finite probability values.

record NatProbability : Set where
  constructor prob
  field
    numerator : Nat
    denominator : Nat

open NatProbability public

zeroProbability : NatProbability
zeroProbability = prob zero (suc zero)

oneProbability : NatProbability
oneProbability = prob (suc zero) (suc zero)

_+P_ : NatProbability → NatProbability → NatProbability
prob n d +P prob m _ = prob (n + m) d

projectionProbability : BasisProjection → TwoState → NatProbability
projectionProbability projectKet0 ket0 = oneProbability
projectionProbability projectKet0 ket1 = zeroProbability
projectionProbability projectKet1 ket0 = zeroProbability
projectionProbability projectKet1 ket1 = oneProbability

basisProjectionTotal :
  (ψ : TwoState) →
  projectionProbability projectKet0 ψ +P
  projectionProbability projectKet1 ψ
  ≡ oneProbability
basisProjectionTotal ket0 = refl
basisProjectionTotal ket1 = refl

------------------------------------------------------------------------
-- Finite norm and identity evolution.

normSquared : TwoState → Nat
normSquared ket0 = suc zero
normSquared ket1 = suc zero

record NormalizedFiniteState : Set where
  constructor normalized
  field
    carrierState : TwoState
    normSquaredIsOne : normSquared carrierState ≡ suc zero

open NormalizedFiniteState public

normalizedKet0 : NormalizedFiniteState
normalizedKet0 =
  normalized ket0 refl

normalizedKet1 : NormalizedFiniteState
normalizedKet1 =
  normalized ket1 refl

TimeStep : Set
TimeStep = Nat

identityEvolution : TimeStep → TwoState → TwoState
identityEvolution _ ψ = ψ

identityEvolutionPreservesNorm :
  (t : TimeStep) →
  (ψ : TwoState) →
  normSquared (identityEvolution t ψ) ≡ normSquared ψ
identityEvolutionPreservesNorm _ ket0 = refl
identityEvolutionPreservesNorm _ ket1 = refl

identityEvolutionPreservesNormalization :
  (t : TimeStep) →
  (ψ : NormalizedFiniteState) →
  normSquared (identityEvolution t (carrierState ψ)) ≡ suc zero
identityEvolutionPreservesNormalization t ψ =
  normSquaredIsOne ψ

record FiniteUnitaryEvolutionToken : Set where
  field
    evolution : TimeStep → TwoState → TwoState
    inverseEvolution : TimeStep → TwoState → TwoState
    leftInverse :
      (t : TimeStep) →
      (ψ : TwoState) →
      inverseEvolution t (evolution t ψ) ≡ ψ
    rightInverse :
      (t : TimeStep) →
      (ψ : TwoState) →
      evolution t (inverseEvolution t ψ) ≡ ψ
    preservesNorm :
      (t : TimeStep) →
      (ψ : TwoState) →
      normSquared (evolution t ψ) ≡ normSquared ψ

open FiniteUnitaryEvolutionToken public

identityUnitaryEvolutionToken : FiniteUnitaryEvolutionToken
identityUnitaryEvolutionToken =
  record
    { evolution = identityEvolution
    ; inverseEvolution = identityEvolution
    ; leftInverse = λ _ ψ → refl
    ; rightInverse = λ _ ψ → refl
    ; preservesNorm = identityEvolutionPreservesNorm
    }

------------------------------------------------------------------------
-- Symbolic zero Hamiltonian self-adjointness over the two-state basis.

zeroHamiltonianMatrixEntry : TwoState → TwoState → Nat
zeroHamiltonianMatrixEntry _ _ = zero

record ZeroHamiltonianSelfAdjointToken : Set where
  field
    diagonal00IsZero :
      zeroHamiltonianMatrixEntry ket0 ket0 ≡ zero
    diagonal11IsZero :
      zeroHamiltonianMatrixEntry ket1 ket1 ≡ zero
    offDiagonal01IsZero :
      zeroHamiltonianMatrixEntry ket0 ket1 ≡ zero
    offDiagonal10IsZero :
      zeroHamiltonianMatrixEntry ket1 ket0 ≡ zero
    symmetricMatrixEntries :
      (ψ φ : TwoState) →
      zeroHamiltonianMatrixEntry ψ φ ≡
      zeroHamiltonianMatrixEntry φ ψ

open ZeroHamiltonianSelfAdjointToken public

zeroHamiltonianSelfAdjointToken : ZeroHamiltonianSelfAdjointToken
zeroHamiltonianSelfAdjointToken =
  record
    { diagonal00IsZero = refl
    ; diagonal11IsZero = refl
    ; offDiagonal01IsZero = refl
    ; offDiagonal10IsZero = refl
    ; symmetricMatrixEntries = λ _ _ → refl
    }

------------------------------------------------------------------------
-- Finite Born adapter receipt.

record FiniteBornProjectionSemantics : Set where
  field
    probability :
      BasisProjection → TwoState → NatProbability
    probabilityTotal :
      (ψ : TwoState) →
      probability projectKet0 ψ +P probability projectKet1 ψ
      ≡ oneProbability
    basis0ProbabilityOnKet0 :
      probability projectKet0 ket0 ≡ oneProbability
    basis1ProbabilityOnKet0 :
      probability projectKet1 ket0 ≡ zeroProbability
    basis0ProbabilityOnKet1 :
      probability projectKet0 ket1 ≡ zeroProbability
    basis1ProbabilityOnKet1 :
      probability projectKet1 ket1 ≡ oneProbability

open FiniteBornProjectionSemantics public

canonicalFiniteBornProjectionSemantics :
  FiniteBornProjectionSemantics
canonicalFiniteBornProjectionSemantics =
  record
    { probability = projectionProbability
    ; probabilityTotal = basisProjectionTotal
    ; basis0ProbabilityOnKet0 = refl
    ; basis1ProbabilityOnKet0 = refl
    ; basis0ProbabilityOnKet1 = refl
    ; basis1ProbabilityOnKet1 = refl
    }

record FiniteQuantumSchrodingerBornAdapter : Set₁ where
  field
    upstreamQuantumObligations :
      Quantum.QuantumQFTPromotionObligationReceipt
    states : List TwoState
    normalizedBasisStates : List NormalizedFiniteState
    unitaryEvolutionToken : FiniteUnitaryEvolutionToken
    zeroHamiltonianToken : ZeroHamiltonianSelfAdjointToken
    bornProjectionSemantics : FiniteBornProjectionSemantics
    finiteToyScope : Bool
    finiteToyScopeIsTrue : finiteToyScope ≡ true
    twoStateCarrierOnly : Bool
    twoStateCarrierOnlyIsTrue : twoStateCarrierOnly ≡ true
    fullHilbertDomainSupplied : Bool
    fullHilbertDomainSuppliedIsFalse :
      fullHilbertDomainSupplied ≡ false
    stoneTheoremDischarged : Bool
    stoneTheoremDischargedIsFalse :
      stoneTheoremDischarged ≡ false
    empiricalQuantumSemanticsAccepted : Bool
    empiricalQuantumSemanticsAcceptedIsFalse :
      empiricalQuantumSemanticsAccepted ≡ false
    promotesFullSchrodingerDynamics : Bool
    promotesFullSchrodingerDynamicsIsFalse :
      promotesFullSchrodingerDynamics ≡ false
    promotesFullBornSemantics : Bool
    promotesFullBornSemanticsIsFalse :
      promotesFullBornSemantics ≡ false
    promotesQFT : Bool
    promotesQFTIsFalse :
      promotesQFT ≡ false
    boundaryNotes : List String

open FiniteQuantumSchrodingerBornAdapter public

canonicalFiniteQuantumSchrodingerBornAdapter :
  FiniteQuantumSchrodingerBornAdapter
canonicalFiniteQuantumSchrodingerBornAdapter =
  record
    { upstreamQuantumObligations =
        Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; states = ket0 ∷ ket1 ∷ []
    ; normalizedBasisStates =
        normalizedKet0 ∷ normalizedKet1 ∷ []
    ; unitaryEvolutionToken =
        identityUnitaryEvolutionToken
    ; zeroHamiltonianToken =
        zeroHamiltonianSelfAdjointToken
    ; bornProjectionSemantics =
        canonicalFiniteBornProjectionSemantics
    ; finiteToyScope = true
    ; finiteToyScopeIsTrue = refl
    ; twoStateCarrierOnly = true
    ; twoStateCarrierOnlyIsTrue = refl
    ; fullHilbertDomainSupplied = false
    ; fullHilbertDomainSuppliedIsFalse = refl
    ; stoneTheoremDischarged = false
    ; stoneTheoremDischargedIsFalse = refl
    ; empiricalQuantumSemanticsAccepted = false
    ; empiricalQuantumSemanticsAcceptedIsFalse = refl
    ; promotesFullSchrodingerDynamics = false
    ; promotesFullSchrodingerDynamicsIsFalse = refl
    ; promotesFullBornSemantics = false
    ; promotesFullBornSemanticsIsFalse = refl
    ; promotesQFT = false
    ; promotesQFTIsFalse = refl
    ; boundaryNotes =
        "Finite two-state carrier only"
        ∷ "Identity evolution is unitary by definitional equality"
        ∷ "Zero Hamiltonian is self-adjoint only as a finite symbolic matrix"
        ∷ "Born normalization is proved only for basis projections on basis states"
        ∷ "No dense domain, Stone theorem, continuum Hilbert space, empirical semantics, POVM semantics, or QFT construction is supplied"
        ∷ []
    }

------------------------------------------------------------------------
-- Canonical adapter lemmas.

canonicalKet0NormPreserved :
  (t : TimeStep) →
  normSquared
    (evolution
      (unitaryEvolutionToken canonicalFiniteQuantumSchrodingerBornAdapter)
      t
      ket0)
  ≡ normSquared ket0
canonicalKet0NormPreserved t =
  preservesNorm
    (unitaryEvolutionToken canonicalFiniteQuantumSchrodingerBornAdapter)
    t
    ket0

canonicalKet1NormPreserved :
  (t : TimeStep) →
  normSquared
    (evolution
      (unitaryEvolutionToken canonicalFiniteQuantumSchrodingerBornAdapter)
      t
      ket1)
  ≡ normSquared ket1
canonicalKet1NormPreserved t =
  preservesNorm
    (unitaryEvolutionToken canonicalFiniteQuantumSchrodingerBornAdapter)
    t
    ket1

canonicalBornProbabilityTotal :
  (ψ : TwoState) →
  probability
    (bornProjectionSemantics canonicalFiniteQuantumSchrodingerBornAdapter)
    projectKet0
    ψ
  +P
  probability
    (bornProjectionSemantics canonicalFiniteQuantumSchrodingerBornAdapter)
    projectKet1
    ψ
  ≡ oneProbability
canonicalBornProbabilityTotal ψ =
  probabilityTotal
    (bornProjectionSemantics canonicalFiniteQuantumSchrodingerBornAdapter)
    ψ

canonicalAdapterKeepsQuantumDynamicsFalse :
  Quantum.quantumDynamicsPromoted
    Quantum.canonicalQuantumQFTPromotionObligationReceipt
  ≡ false
canonicalAdapterKeepsQuantumDynamicsFalse =
  Quantum.quantumDynamicsPromotedIsFalse
    Quantum.canonicalQuantumQFTPromotionObligationReceipt

canonicalAdapterKeepsBornRuleFalse :
  Quantum.bornRulePromoted
    Quantum.canonicalQuantumQFTPromotionObligationReceipt
  ≡ false
canonicalAdapterKeepsBornRuleFalse =
  Quantum.bornRulePromotedIsFalse
    Quantum.canonicalQuantumQFTPromotionObligationReceipt

canonicalAdapterKeepsQFTFalse :
  Quantum.qftPromoted
    Quantum.canonicalQuantumQFTPromotionObligationReceipt
  ≡ false
canonicalAdapterKeepsQFTFalse =
  Quantum.qftPromotedIsFalse
    Quantum.canonicalQuantumQFTPromotionObligationReceipt

canonicalAdapterPromotesFullSchrodingerDynamicsFalse :
  promotesFullSchrodingerDynamics
    canonicalFiniteQuantumSchrodingerBornAdapter
  ≡ false
canonicalAdapterPromotesFullSchrodingerDynamicsFalse =
  promotesFullSchrodingerDynamicsIsFalse
    canonicalFiniteQuantumSchrodingerBornAdapter

canonicalAdapterPromotesFullBornSemanticsFalse :
  promotesFullBornSemantics
    canonicalFiniteQuantumSchrodingerBornAdapter
  ≡ false
canonicalAdapterPromotesFullBornSemanticsFalse =
  promotesFullBornSemanticsIsFalse
    canonicalFiniteQuantumSchrodingerBornAdapter

canonicalAdapterPromotesQFTFalse :
  promotesQFT canonicalFiniteQuantumSchrodingerBornAdapter
  ≡ false
canonicalAdapterPromotesQFTFalse =
  promotesQFTIsFalse canonicalFiniteQuantumSchrodingerBornAdapter
