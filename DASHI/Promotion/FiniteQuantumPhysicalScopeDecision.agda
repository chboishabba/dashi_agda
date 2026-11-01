module DASHI.Promotion.FiniteQuantumPhysicalScopeDecision where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.FiniteQuantumSchrodingerBornAdapter as Finite
import DASHI.Promotion.QuantumFiniteToGeneralBoundary as Boundary
import DASHI.Promotion.QuantumQFTObligations as Quantum

------------------------------------------------------------------------
-- Explicit finite-mode Schrodinger/Born scope decision.
--
-- This surface separates the inhabited finite physical computation lane
-- from the still-false infinite-dimensional promotion lane.  A finite
-- Hilbert carrier is accepted as sufficient for the local finite-mode
-- computations recorded by the adapter: state enumeration, basis-state
-- normalization, identity unitary evolution, the symbolic zero Hamiltonian,
-- and basis-projection Born totals.  It is not evidence for the infinite
-- Hilbert completion, unbounded-operator domain, Stone theorem, spectral
-- calculus, general Born semantics, or QFT promotion obligations.

data FiniteModeComputation : Set where
  finiteStateEnumeration : FiniteModeComputation
  finiteBasisNormalization : FiniteModeComputation
  finiteIdentityUnitaryEvolution : FiniteModeComputation
  finiteZeroHamiltonianMatrix : FiniteModeComputation
  finiteBasisBornProbabilityTotal : FiniteModeComputation

data GeneralPromotionBlocker : Set where
  infiniteHilbertCompletionBlocker : GeneralPromotionBlocker
  unboundedOperatorDomainBlocker : GeneralPromotionBlocker
  stoneTheoremBlocker : GeneralPromotionBlocker
  spectralCalculusBlocker : GeneralPromotionBlocker
  generalPOVMSemanticsBlocker : GeneralPromotionBlocker
  empiricalCalibrationBlocker : GeneralPromotionBlocker
  qftConstructionBlocker : GeneralPromotionBlocker

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

finiteModeComputations : List FiniteModeComputation
finiteModeComputations =
  finiteStateEnumeration
  ∷ finiteBasisNormalization
  ∷ finiteIdentityUnitaryEvolution
  ∷ finiteZeroHamiltonianMatrix
  ∷ finiteBasisBornProbabilityTotal
  ∷ []

generalPromotionBlockers : List GeneralPromotionBlocker
generalPromotionBlockers =
  infiniteHilbertCompletionBlocker
  ∷ unboundedOperatorDomainBlocker
  ∷ stoneTheoremBlocker
  ∷ spectralCalculusBlocker
  ∷ generalPOVMSemanticsBlocker
  ∷ empiricalCalibrationBlocker
  ∷ qftConstructionBlocker
  ∷ []

record FiniteQuantumPhysicalScopeDecision : Set₁ where
  field
    decisionLabel : String
    finiteAdapter :
      Finite.FiniteQuantumSchrodingerBornAdapter
    finiteToGeneralBoundary :
      Boundary.QuantumFiniteToGeneralBoundary
    upstreamQuantumObligations :
      Quantum.QuantumQFTPromotionObligationReceipt
    finiteComputations : List FiniteModeComputation
    generalBlockers : List GeneralPromotionBlocker

    finiteStateCarrierCount : Nat
    finiteStateCarrierCountIs2 :
      finiteStateCarrierCount ≡
      listLength (Finite.states finiteAdapter)
    normalizedFiniteBasisCount : Nat
    normalizedFiniteBasisCountIs2 :
      normalizedFiniteBasisCount ≡
      listLength (Finite.normalizedBasisStates finiteAdapter)
    finiteComputationCount : Nat
    finiteComputationCountIs5 :
      finiteComputationCount ≡
      listLength finiteComputations
    generalBlockerCount : Nat
    generalBlockerCountIs7 :
      generalBlockerCount ≡
      listLength generalBlockers
    boundaryLiftObligationCount : Nat
    boundaryLiftObligationCountIs8 :
      boundaryLiftObligationCount ≡
      Boundary.liftObligationCount finiteToGeneralBoundary

    finiteHilbertCarrierSufficientForFiniteModePhysics : Bool
    finiteHilbertCarrierSufficientForFiniteModePhysicsIsTrue :
      finiteHilbertCarrierSufficientForFiniteModePhysics ≡ true
    finiteSchrodingerBornComputationAccepted : Bool
    finiteSchrodingerBornComputationAcceptedIsTrue :
      finiteSchrodingerBornComputationAccepted ≡ true

    infiniteHilbertPromotion : Bool
    infiniteHilbertPromotionIsFalse :
      infiniteHilbertPromotion ≡ false
    unboundedOperatorPromotion : Bool
    unboundedOperatorPromotionIsFalse :
      unboundedOperatorPromotion ≡ false
    stoneTheoremPromotion : Bool
    stoneTheoremPromotionIsFalse :
      stoneTheoremPromotion ≡ false
    spectralTheoremPromotion : Bool
    spectralTheoremPromotionIsFalse :
      spectralTheoremPromotion ≡ false
    generalBornPromotion : Bool
    generalBornPromotionIsFalse :
      generalBornPromotion ≡ false
    qftPromotion : Bool
    qftPromotionIsFalse :
      qftPromotion ≡ false
    terminalPromotion : Bool
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    decisionNotes : List String

open FiniteQuantumPhysicalScopeDecision public

canonicalFiniteQuantumPhysicalScopeDecision :
  FiniteQuantumPhysicalScopeDecision
canonicalFiniteQuantumPhysicalScopeDecision =
  record
    { decisionLabel =
        "finite-mode Schrodinger/Born physical scope decision"
    ; finiteAdapter =
        Finite.canonicalFiniteQuantumSchrodingerBornAdapter
    ; finiteToGeneralBoundary =
        Boundary.canonicalQuantumFiniteToGeneralBoundary
    ; upstreamQuantumObligations =
        Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; finiteComputations =
        finiteModeComputations
    ; generalBlockers =
        generalPromotionBlockers
    ; finiteStateCarrierCount =
        2
    ; finiteStateCarrierCountIs2 =
        refl
    ; normalizedFiniteBasisCount =
        2
    ; normalizedFiniteBasisCountIs2 =
        refl
    ; finiteComputationCount =
        5
    ; finiteComputationCountIs5 =
        refl
    ; generalBlockerCount =
        7
    ; generalBlockerCountIs7 =
        refl
    ; boundaryLiftObligationCount =
        8
    ; boundaryLiftObligationCountIs8 =
        refl
    ; finiteHilbertCarrierSufficientForFiniteModePhysics =
        true
    ; finiteHilbertCarrierSufficientForFiniteModePhysicsIsTrue =
        refl
    ; finiteSchrodingerBornComputationAccepted =
        true
    ; finiteSchrodingerBornComputationAcceptedIsTrue =
        refl
    ; infiniteHilbertPromotion =
        false
    ; infiniteHilbertPromotionIsFalse =
        refl
    ; unboundedOperatorPromotion =
        false
    ; unboundedOperatorPromotionIsFalse =
        refl
    ; stoneTheoremPromotion =
        false
    ; stoneTheoremPromotionIsFalse =
        refl
    ; spectralTheoremPromotion =
        false
    ; spectralTheoremPromotionIsFalse =
        refl
    ; generalBornPromotion =
        false
    ; generalBornPromotionIsFalse =
        refl
    ; qftPromotion =
        false
    ; qftPromotionIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; decisionNotes =
        "finite Hilbert carrier is sufficient for finite-mode norm, identity-evolution, zero-Hamiltonian, and basis Born computations"
        ∷ "finite sufficiency is not an infinite-dimensional Hilbert completion or dense-domain witness"
        ∷ "Stone theorem, spectral calculus, and unbounded-operator promotion remain false"
        ∷ "general Born semantics and QFT promotion remain false"
        ∷ []
    }

canonicalFiniteStateCarrierCountIs2 :
  finiteStateCarrierCount
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ 2
canonicalFiniteStateCarrierCountIs2 = refl

canonicalNormalizedFiniteBasisCountIs2 :
  normalizedFiniteBasisCount
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ 2
canonicalNormalizedFiniteBasisCountIs2 = refl

canonicalFiniteComputationCountIs5 :
  finiteComputationCount
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ 5
canonicalFiniteComputationCountIs5 = refl

canonicalGeneralBlockerCountIs7 :
  generalBlockerCount
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ 7
canonicalGeneralBlockerCountIs7 = refl

canonicalBoundaryLiftObligationCountStill8 :
  boundaryLiftObligationCount
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ 8
canonicalBoundaryLiftObligationCountStill8 = refl

canonicalFiniteHilbertCarrierSufficient :
  finiteHilbertCarrierSufficientForFiniteModePhysics
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ true
canonicalFiniteHilbertCarrierSufficient = refl

canonicalFiniteSchrodingerBornComputationAccepted :
  finiteSchrodingerBornComputationAccepted
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ true
canonicalFiniteSchrodingerBornComputationAccepted = refl

canonicalInfiniteHilbertPromotionFalse :
  infiniteHilbertPromotion
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ false
canonicalInfiniteHilbertPromotionFalse = refl

canonicalUnboundedOperatorPromotionFalse :
  unboundedOperatorPromotion
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ false
canonicalUnboundedOperatorPromotionFalse = refl

canonicalStoneTheoremPromotionFalse :
  stoneTheoremPromotion
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ false
canonicalStoneTheoremPromotionFalse = refl

canonicalSpectralTheoremPromotionFalse :
  spectralTheoremPromotion
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ false
canonicalSpectralTheoremPromotionFalse = refl

canonicalGeneralBornPromotionFalse :
  generalBornPromotion
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ false
canonicalGeneralBornPromotionFalse = refl

canonicalQFTPromotionFalse :
  qftPromotion
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ false
canonicalQFTPromotionFalse = refl

canonicalTerminalPromotionFalse :
  terminalPromotion
    canonicalFiniteQuantumPhysicalScopeDecision
  ≡ false
canonicalTerminalPromotionFalse = refl

canonicalUpstreamQuantumDynamicsStillFalse :
  Quantum.quantumDynamicsPromoted
    (upstreamQuantumObligations
      canonicalFiniteQuantumPhysicalScopeDecision)
  ≡ false
canonicalUpstreamQuantumDynamicsStillFalse =
  Quantum.quantumDynamicsPromotedIsFalse
    (upstreamQuantumObligations
      canonicalFiniteQuantumPhysicalScopeDecision)

canonicalUpstreamBornRuleStillFalse :
  Quantum.bornRulePromoted
    (upstreamQuantumObligations
      canonicalFiniteQuantumPhysicalScopeDecision)
  ≡ false
canonicalUpstreamBornRuleStillFalse =
  Quantum.bornRulePromotedIsFalse
    (upstreamQuantumObligations
      canonicalFiniteQuantumPhysicalScopeDecision)

canonicalUpstreamQFTStillFalse :
  Quantum.qftPromoted
    (upstreamQuantumObligations
      canonicalFiniteQuantumPhysicalScopeDecision)
  ≡ false
canonicalUpstreamQFTStillFalse =
  Quantum.qftPromotedIsFalse
    (upstreamQuantumObligations
      canonicalFiniteQuantumPhysicalScopeDecision)
