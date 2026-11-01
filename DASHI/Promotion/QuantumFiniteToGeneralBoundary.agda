module DASHI.Promotion.QuantumFiniteToGeneralBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter as Finite
import DASHI.Promotion.QuantumQFTObligations as Quantum

------------------------------------------------------------------------
-- Boundary between the inhabited finite adapter and full quantum claims.
--
-- The finite adapter proves a real two-state fact: basis states have
-- unit norm under identity evolution and basis-projection Born
-- probabilities total to one.  This module records exactly what that
-- evidence is allowed to discharge and what remains required before
-- Schrodinger dynamics, Born semantics, or QFT can be promoted.

data FiniteEvidenceKind : Set where
  twoStateNormEvidence : FiniteEvidenceKind
  twoStateBornTotalEvidence : FiniteEvidenceKind

data LiftObligationKind : Set where
  denseHilbertDomainLift : LiftObligationKind
  unboundedHamiltonianDomainLift : LiftObligationKind
  selfAdjointnessProofLift : LiftObligationKind
  stoneTheoremLift : LiftObligationKind
  spectralTheoremExponentialLift : LiftObligationKind
  povmSigmaAlgebraLift : LiftObligationKind
  repeatedMeasureLawLift : LiftObligationKind
  empiricalCalibrationLift : LiftObligationKind

record FiniteEvidenceRow : Set₁ where
  field
    rowLabel : String
    evidenceKinds : List FiniteEvidenceKind
    finiteAdapter :
      Finite.FiniteQuantumSchrodingerBornAdapter
    normalizedStates : List Finite.NormalizedFiniteState
    normPreservedKet0 :
      (t : Finite.TimeStep) →
      Finite.normSquared
        (Finite.evolution
          (Finite.unitaryEvolutionToken finiteAdapter)
          t
          Finite.ket0)
      ≡ Finite.normSquared Finite.ket0
    normPreservedKet1 :
      (t : Finite.TimeStep) →
      Finite.normSquared
        (Finite.evolution
          (Finite.unitaryEvolutionToken finiteAdapter)
          t
          Finite.ket1)
      ≡ Finite.normSquared Finite.ket1
    bornProbabilityTotal :
      (ψ : Finite.TwoState) →
      Finite.probability
        (Finite.bornProjectionSemantics finiteAdapter)
        Finite.projectKet0
        ψ
      Finite.+P
      Finite.probability
        (Finite.bornProjectionSemantics finiteAdapter)
        Finite.projectKet1
        ψ
      ≡ Finite.oneProbability
    finiteOnly : Bool
    finiteOnlyIsTrue : finiteOnly ≡ true
    validationCommand : String

open FiniteEvidenceRow public

record LiftObligationRow : Set₁ where
  field
    rowLabel : String
    kind : LiftObligationKind
    target : Quantum.QuantumPromotionTarget
    family : Quantum.QuantumObligationFamily
    requiredToken : String
    sourceQuantumRow : String
    whyFiniteEvidenceInsufficient : String
    guardToKeepFalse : Quantum.PromotionGuard
    currentState : Quantum.ObligationState
    dischargedByFiniteAdapter : Bool
    dischargedByFiniteAdapterIsFalse :
      dischargedByFiniteAdapter ≡ false
    validationCommand : String

open LiftObligationRow public

mkLiftRow :
  String →
  LiftObligationKind →
  Quantum.QuantumPromotionTarget →
  Quantum.QuantumObligationFamily →
  String →
  String →
  String →
  Quantum.PromotionGuard →
  Quantum.ObligationState →
  String →
  LiftObligationRow
mkLiftRow label kind target family token source reason guard state command =
  record
    { rowLabel = label
    ; kind = kind
    ; target = target
    ; family = family
    ; requiredToken = token
    ; sourceQuantumRow = source
    ; whyFiniteEvidenceInsufficient = reason
    ; guardToKeepFalse = guard
    ; currentState = state
    ; dischargedByFiniteAdapter = false
    ; dischargedByFiniteAdapterIsFalse = refl
    ; validationCommand = command
    }

listCount : ∀ {A : Set₁} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalFiniteEvidenceRow : FiniteEvidenceRow
canonicalFiniteEvidenceRow =
  record
    { rowLabel =
        "finite two-state norm and Born total evidence"
    ; evidenceKinds =
        twoStateNormEvidence ∷ twoStateBornTotalEvidence ∷ []
    ; finiteAdapter =
        Finite.canonicalFiniteQuantumSchrodingerBornAdapter
    ; normalizedStates =
        Finite.normalizedKet0 ∷ Finite.normalizedKet1 ∷ []
    ; normPreservedKet0 =
        Finite.canonicalKet0NormPreserved
    ; normPreservedKet1 =
        Finite.canonicalKet1NormPreserved
    ; bornProbabilityTotal =
        Finite.canonicalBornProbabilityTotal
    ; finiteOnly =
        true
    ; finiteOnlyIsTrue =
        refl
    ; validationCommand =
        "agda -i . DASHI/Promotion/FiniteQuantumSchrodingerBornAdapter.agda"
    }

canonicalLiftObligationRows : List LiftObligationRow
canonicalLiftObligationRows =
  mkLiftRow
    "dense Hilbert domain lift"
    denseHilbertDomainLift
    Quantum.schrodingerDynamicsTarget
    Quantum.hilbertRepresentationFamily
    "PhysicalHilbertRepresentationToken"
    "Schrodinger Hilbert representation"
    "two basis states do not supply completion, inner product, or dense physical domain"
    Quantum.quantumDynamicsPromotedGuard
    Quantum.proofRequired
    "agda -i . DASHI/Physics/Closure/SchrodingerEvolutionScope.agda"
  ∷ mkLiftRow
    "unbounded Hamiltonian domain lift"
    unboundedHamiltonianDomainLift
    Quantum.schrodingerDynamicsTarget
    Quantum.selfAdjointHamiltonianFamily
    "DenseHamiltonianDomainToken"
    "Schrodinger self-adjoint Hamiltonian"
    "the finite zero matrix has total finite domain and does not identify an unbounded physical operator domain"
    Quantum.quantumDynamicsPromotedGuard
    Quantum.proofRequired
    "agda -i . DASHI/Physics/Closure/SchrodingerSelfAdjointEvolutionReceipt.agda"
  ∷ mkLiftRow
    "self-adjointness proof lift"
    selfAdjointnessProofLift
    Quantum.schrodingerDynamicsTarget
    Quantum.selfAdjointHamiltonianFamily
    "SelfAdjointHamiltonianToken"
    "Schrodinger self-adjoint Hamiltonian"
    "symbolic finite symmetry is not an essential self-adjointness or Kato-Rellich theorem"
    Quantum.quantumDynamicsPromotedGuard
    Quantum.proofRequired
    "agda -i . DASHI/Physics/Closure/SchrodingerSelfAdjointEvolutionReceipt.agda"
  ∷ mkLiftRow
    "Stone theorem lift"
    stoneTheoremLift
    Quantum.schrodingerDynamicsTarget
    Quantum.stoneUnitaryEvolutionFamily
    "StoneStronglyContinuousUnitaryGroupToken"
    "Stone/unitary Schrodinger evolution"
    "identity evolution on two states does not construct a strongly continuous one-parameter unitary group from a generator"
    Quantum.quantumDynamicsPromotedGuard
    Quantum.proofRequired
    "agda -i . DASHI/Quantum/Stone.agda"
  ∷ mkLiftRow
    "spectral theorem exponential lift"
    spectralTheoremExponentialLift
    Quantum.schrodingerDynamicsTarget
    Quantum.exponentialConstructionFamily
    "SpectralTheoremExpMinusITHOverHbarToken"
    "Schrodinger exponential construction"
    "finite identity dynamics does not construct exp(-i t H / hbar) by spectral calculus for the target Hamiltonian"
    Quantum.quantumDynamicsPromotedGuard
    Quantum.proofRequired
    "agda -i . DASHI/Physics/SchrodingerAssumedTheorem.agda"
  ∷ mkLiftRow
    "POVM sigma-algebra lift"
    povmSigmaAlgebraLift
    Quantum.bornSemanticsTarget
    Quantum.povmProbabilityFamily
    "POVMProbabilityMeasureToken"
    "Born POVM probability semantics"
    "two basis projections do not supply an outcome sigma-algebra or POVM probability measure laws"
    Quantum.bornRulePromotedGuard
    Quantum.proofRequired
    "agda -i . DASHI/Physics/Measurement.agda"
  ∷ mkLiftRow
    "repeated-measure law lift"
    repeatedMeasureLawLift
    Quantum.bornSemanticsTarget
    Quantum.statisticalSemanticsFamily
    "RepeatedMeasurementCalibrationToken"
    "Born statistical and empirical semantics"
    "basis probability totals do not interpret repeated trials, uncertainty, or provider comparison"
    Quantum.quantumEmpiricalAdequacyGuard
    Quantum.empiricalValidationRequired
    "agda -i . DASHI/Physics/Prediction.agda"
  ∷ mkLiftRow
    "empirical calibration lift"
    empiricalCalibrationLift
    Quantum.schrodingerDynamicsTarget
    Quantum.observableCalibrationFamily
    "SchrodingerObservableCalibrationToken"
    "Schrodinger observable calibration"
    "finite symbolic probabilities do not bind hbar, masses, units, observables, or empirical authority"
    Quantum.quantumDynamicsPromotedGuard
    Quantum.adapterRequired
    "agda -i . DASHI/Constants/Registry.agda"
  ∷ []

record QuantumFiniteToGeneralBoundary : Set₁ where
  field
    boundaryLabel : String
    upstreamQuantumObligations :
      Quantum.QuantumQFTPromotionObligationReceipt
    finiteEvidence : FiniteEvidenceRow
    liftObligations : List LiftObligationRow
    finiteEvidenceRowCount : Nat
    finiteEvidenceRowCountIs1 :
      finiteEvidenceRowCount ≡ 1
    liftObligationCount : Nat
    liftObligationCountIs8 :
      liftObligationCount ≡ 8
    finiteAdapterPromotesSchrodinger : Bool
    finiteAdapterPromotesSchrodingerIsFalse :
      finiteAdapterPromotesSchrodinger ≡ false
    finiteAdapterPromotesBorn : Bool
    finiteAdapterPromotesBornIsFalse :
      finiteAdapterPromotesBorn ≡ false
    finiteAdapterPromotesQFT : Bool
    finiteAdapterPromotesQFTIsFalse :
      finiteAdapterPromotesQFT ≡ false
    upstreamSchrodingerPromoted : Bool
    upstreamSchrodingerPromotedIsFalse :
      upstreamSchrodingerPromoted ≡ false
    upstreamBornPromoted : Bool
    upstreamBornPromotedIsFalse :
      upstreamBornPromoted ≡ false
    upstreamQFTPromoted : Bool
    upstreamQFTPromotedIsFalse :
      upstreamQFTPromoted ≡ false
    promotionDecision : String
    validationCommand : String
    boundaryNotes : List String

open QuantumFiniteToGeneralBoundary public

canonicalQuantumFiniteToGeneralBoundary :
  QuantumFiniteToGeneralBoundary
canonicalQuantumFiniteToGeneralBoundary =
  record
    { boundaryLabel =
        "canonical finite-to-general quantum promotion boundary"
    ; upstreamQuantumObligations =
        Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; finiteEvidence =
        canonicalFiniteEvidenceRow
    ; liftObligations =
        canonicalLiftObligationRows
    ; finiteEvidenceRowCount =
        1
    ; finiteEvidenceRowCountIs1 =
        refl
    ; liftObligationCount =
        listCount canonicalLiftObligationRows
    ; liftObligationCountIs8 =
        refl
    ; finiteAdapterPromotesSchrodinger =
        Finite.promotesFullSchrodingerDynamics
          Finite.canonicalFiniteQuantumSchrodingerBornAdapter
    ; finiteAdapterPromotesSchrodingerIsFalse =
        Finite.canonicalAdapterPromotesFullSchrodingerDynamicsFalse
    ; finiteAdapterPromotesBorn =
        Finite.promotesFullBornSemantics
          Finite.canonicalFiniteQuantumSchrodingerBornAdapter
    ; finiteAdapterPromotesBornIsFalse =
        Finite.canonicalAdapterPromotesFullBornSemanticsFalse
    ; finiteAdapterPromotesQFT =
        Finite.promotesQFT
          Finite.canonicalFiniteQuantumSchrodingerBornAdapter
    ; finiteAdapterPromotesQFTIsFalse =
        Finite.canonicalAdapterPromotesQFTFalse
    ; upstreamSchrodingerPromoted =
        Quantum.quantumDynamicsPromoted
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamSchrodingerPromotedIsFalse =
        Quantum.quantumDynamicsPromotedIsFalse
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamBornPromoted =
        Quantum.bornRulePromoted
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamBornPromotedIsFalse =
        Quantum.bornRulePromotedIsFalse
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamQFTPromoted =
        Quantum.qftPromoted
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; upstreamQFTPromotedIsFalse =
        Quantum.qftPromotedIsFalse
          Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; promotionDecision =
        "hold"
    ; validationCommand =
        "agda -i . DASHI/Promotion/QuantumFiniteToGeneralBoundary.agda"
    ; boundaryNotes =
        "finite evidence proves only two-state norm preservation and basis Born totals"
        ∷ "full Schrodinger promotion still needs Hilbert/domain/self-adjoint/Stone/spectral-calculus evidence"
        ∷ "full Born promotion still needs POVM, sigma-algebra, repeated-measure, and empirical semantics"
        ∷ "QFT promotion receives no discharge from the finite adapter"
        ∷ []
    }

canonicalFiniteEvidenceRowCountIs1 :
  QuantumFiniteToGeneralBoundary.finiteEvidenceRowCount
    canonicalQuantumFiniteToGeneralBoundary
  ≡ 1
canonicalFiniteEvidenceRowCountIs1 = refl

canonicalLiftObligationCountIs8 :
  QuantumFiniteToGeneralBoundary.liftObligationCount
    canonicalQuantumFiniteToGeneralBoundary
  ≡ 8
canonicalLiftObligationCountIs8 = refl

canonicalBoundaryKeepsFiniteSchrodingerPromotionFalse :
  QuantumFiniteToGeneralBoundary.finiteAdapterPromotesSchrodinger
    canonicalQuantumFiniteToGeneralBoundary
  ≡ false
canonicalBoundaryKeepsFiniteSchrodingerPromotionFalse = refl

canonicalBoundaryKeepsFiniteBornPromotionFalse :
  QuantumFiniteToGeneralBoundary.finiteAdapterPromotesBorn
    canonicalQuantumFiniteToGeneralBoundary
  ≡ false
canonicalBoundaryKeepsFiniteBornPromotionFalse = refl

canonicalBoundaryKeepsFiniteQFTPromotionFalse :
  QuantumFiniteToGeneralBoundary.finiteAdapterPromotesQFT
    canonicalQuantumFiniteToGeneralBoundary
  ≡ false
canonicalBoundaryKeepsFiniteQFTPromotionFalse = refl

canonicalBoundaryKeepsUpstreamSchrodingerPromotionFalse :
  QuantumFiniteToGeneralBoundary.upstreamSchrodingerPromoted
    canonicalQuantumFiniteToGeneralBoundary
  ≡ false
canonicalBoundaryKeepsUpstreamSchrodingerPromotionFalse = refl

canonicalBoundaryKeepsUpstreamBornPromotionFalse :
  QuantumFiniteToGeneralBoundary.upstreamBornPromoted
    canonicalQuantumFiniteToGeneralBoundary
  ≡ false
canonicalBoundaryKeepsUpstreamBornPromotionFalse = refl

canonicalBoundaryKeepsUpstreamQFTPromotionFalse :
  QuantumFiniteToGeneralBoundary.upstreamQFTPromoted
    canonicalQuantumFiniteToGeneralBoundary
  ≡ false
canonicalBoundaryKeepsUpstreamQFTPromotionFalse = refl
