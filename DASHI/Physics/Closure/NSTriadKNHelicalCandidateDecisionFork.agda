module DASHI.Physics.Closure.NSTriadKNHelicalCandidateDecisionFork where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact helical candidate decision fork and remaining analytic
-- cutset".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original dependency theorem.
-- Uses: the global-helicity counterexample, exact scalar-localized
-- reconnaissance, balanced-family phase classification, and triad-phase
-- coherence fallback.
-- Relationship: closes the finite scalar-helicity branch on the represented
-- adversarial family and promotes the phase-coherence operator branch.  The
-- cutoff-uniform PDE estimates and post-quartic completion remain explicit
-- inputs and are not fabricated.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNGlobalHelicityH3DiscriminantCounterexample as Global
import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityExactReconnaissance as Local
import DASHI.Physics.Closure.NSTriadKNFixedSymbolBalancedFamilyReconnaissance as Balanced
import DASHI.Physics.Closure.NSTriadKNTriadPhaseCoherenceFallback as Phase


data CandidateBranch : Set where
  globalHelicity scalarLocalizedHelicity triadPhaseCoherence : CandidateBranch

data FiniteBranchDecision : CandidateBranch → Set where
  globalRejected : FiniteBranchDecision globalHelicity
  scalarLocalizedRejected : FiniteBranchDecision scalarLocalizedHelicity
  phaseCoherencePromoted : FiniteBranchDecision triadPhaseCoherence

globalBranchDecision : FiniteBranchDecision globalHelicity
globalBranchDecision = globalRejected

scalarLocalizedBranchDecision : FiniteBranchDecision scalarLocalizedHelicity
scalarLocalizedBranchDecision = scalarLocalizedRejected

phaseCoherenceBranchDecision : FiniteBranchDecision triadPhaseCoherence
phaseCoherenceBranchDecision = phaseCoherencePromoted

record FiniteDecisionReceipt : Set where
  constructor decision-receipt
  field
    globalReceipt : Global.GlobalHelicityCounterexampleReceipt
    localizedReceipt : Local.LocalizedHelicityExactReceipt
    balancedReceipt : Balanced.BalancedFamilyExactReceipt
    phaseEvidence : Phase.PhaseFallbackFiniteEvidence

open FiniteDecisionReceipt public

finiteDecisionReceipt : FiniteDecisionReceipt
finiteDecisionReceipt =
  decision-receipt
    Global.globalHelicityH3Counterexample
    Local.localizedHelicityExactReceipt
    Balanced.balancedFamilyExactReceipt
    Phase.phaseFallbackFiniteEvidence

record PostQuarticCompletionCutset
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff State Scalar : Set c
    SelectedQuarticFunctional : State → Scalar

    selectedFunctionalCoercive : Set s
    literalGalerkinChainRuleClosed : Set s
    cutoffUniformHarmonicAnalysisClosed : Set s
    strictJointDominationClosed : Set s
    exhaustiveChartCoverageClosed : Set s
    invariantRegionPropagationClosed : Set s
    weightedVorticityExpenditureClosed : Set s
    finiteBKMIntegralClosed : Set s
    cutoffUniformCompactnessClosed : Set s
    nonlinearLimitIdentificationClosed : Set s
    initialDataRecoveryClosed : Set s
    smoothnessBootstrapClosed : Set s
    uniquenessAndContinuationClosed : Set s

open PostQuarticCompletionCutset public
