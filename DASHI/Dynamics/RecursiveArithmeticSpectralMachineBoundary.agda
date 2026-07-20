module DASHI.Dynamics.RecursiveArithmeticSpectralMachineBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.JChartSuccessorBoundary as Charts
import DASHI.Topology.TetrationalGateField as Gates

------------------------------------------------------------------------
-- Hybrid machine surface.
--
-- An LLM may propose candidates, but the machine state separately carries an
-- exact quotient address, continuous/infinitesimal latent state, relational
-- graph, active chart, residual, spectral decomposition, and governance data.

record RecursiveMachine : Set₁ where
  field
    QuotientAddress LatentState RelationGraph Residual SpectralState : Set
    Context Proposal Action Score : Set

    currentAddress : QuotientAddress
    currentLatent : LatentState
    currentRelations : RelationGraph
    currentResidual : Residual
    currentSpectrum : SpectralState
    currentChart : Charts.ChartIndex
    gateField : Gates.GateField

    propose : Context → Proposal
    validateProposal : Proposal → Set
    applyProposal : Proposal → Action → LatentState
    updateAddress : QuotientAddress → Residual → QuotientAddress
    updateRelations : RelationGraph → LatentState → RelationGraph
    updateSpectrum : SpectralState → Residual → SpectralState
    projectResidual : LatentState → Residual
    scoreModel : Charts.ChartIndex → Residual → Score
    rechartDecision : Score → Score → Set
    governanceAdmissible : Proposal → Action → Set

record MachineStep (M : RecursiveMachine) : Set₁ where
  open RecursiveMachine M
  field
    context : Context
    proposal : Proposal
    proposalChecks : proposal ≡ propose context
    proposalValid : validateProposal proposal
    action : Action
    actionAdmissible : governanceAdmissible proposal action
    nextLatent : LatentState
    nextLatentChecks : nextLatent ≡ applyProposal proposal action
    nextResidual : Residual
    nextResidualChecks : nextResidual ≡ projectResidual nextLatent
    nextAddress : QuotientAddress
    nextAddressChecks : nextAddress ≡ updateAddress currentAddress nextResidual
    nextRelations : RelationGraph
    nextRelationsChecks : nextRelations ≡ updateRelations currentRelations nextLatent
    nextSpectrum : SpectralState
    nextSpectrumChecks : nextSpectrum ≡ updateSpectrum currentSpectrum nextResidual

record SearchProcessingProfile : Set where
  constructor searchProcessingProfile
  field
    candidateCount : Nat
    jointContextDimension : Nat
    recursiveDepth : Nat
    interpretation : String

wideDeepMachineProfile : SearchProcessingProfile
wideDeepMachineProfile =
  searchProcessingProfile 27 27 243
    "multiple candidates, broad joint context, and deep recursive checking"

focusedDeepMachineProfile : SearchProcessingProfile
focusedDeepMachineProfile =
  searchProcessingProfile 1 27 243
    "one candidate path with broad and deep internal processing"

record RecursiveMachineBoundary : Set where
  constructor recursiveMachineBoundary
  field
    llmIsWholeMachine : Bool
    llmIsWholeMachineIsFalse : llmIsWholeMachine ≡ false
    proposalEqualsProof : Bool
    proposalEqualsProofIsFalse : proposalEqualsProof ≡ false
    residualAlwaysDiscarded : Bool
    residualAlwaysDiscardedIsFalse : residualAlwaysDiscarded ≡ false
    quotientAndLatentCarriersCollapsed : Bool
    quotientAndLatentCarriersCollapsedIsFalse :
      quotientAndLatentCarriersCollapsed ≡ false
    governancePartOfTransition : Bool
    mdlAndGluingMayTriggerRechart : Bool
    interpretation : String

canonicalRecursiveMachineBoundary : RecursiveMachineBoundary
canonicalRecursiveMachineBoundary =
  recursiveMachineBoundary
    false refl
    false refl
    false refl
    false refl
    true
    true
    "the recursive arithmetic-spectral machine separates proposal generation from exact carriers, validation, residual retention, spectral update, relational memory, governance, and chart selection"
