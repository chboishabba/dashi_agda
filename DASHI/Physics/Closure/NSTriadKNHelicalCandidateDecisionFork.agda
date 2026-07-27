module DASHI.Physics.Closure.NSTriadKNHelicalCandidateDecisionFork where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact helical, matrix-coherence, and direction-coherence decision
-- fork with remaining analytic cutset".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original dependency theorem.
-- Uses: the global/scalar-helicity counterexamples, projected-axis matrix
-- reconnaissance, Constantin--Fefferman direction-coherence interface,
-- triad-direction diagnostics, and the fail-closed Permana audit.
-- Relationship: rejects only the concretely tested projected-axis mode-local
-- family, not every matrix multiplier.  It promotes genuinely triad-coupled
-- direction coherence while leaving functional integrability and all
-- cutoff-uniform PDE estimates explicit and uninhabited.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNGlobalHelicityH3DiscriminantCounterexample as Global
import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityExactReconnaissance as Local
import DASHI.Physics.Closure.NSTriadKNFixedSymbolBalancedFamilyReconnaissance as Balanced
import DASHI.Physics.Closure.NSTriadKNTriadPhaseCoherenceFallback as Phase
import DASHI.Physics.Closure.NSTriadKNMatrixCoherenceExactReconnaissance as Matrix
import DASHI.Physics.Closure.NSTriadKNTriadDirectionAlignmentProgram as Direction
import DASHI.Physics.Closure.NSTriadKNPermanaAlignmentRateAudit as Permana

data CandidateBranch : Set where
  globalHelicity
  scalarLocalizedHelicity
  projectedAxisMatrixCoherence
  complexTriadPhaseCoherence
  triadDirectionCoherence : CandidateBranch

data FiniteBranchDecision : CandidateBranch → Set where
  globalRejected : FiniteBranchDecision globalHelicity
  scalarLocalizedRejected : FiniteBranchDecision scalarLocalizedHelicity
  projectedAxisRejectedOnOptimizedSupport :
    FiniteBranchDecision projectedAxisMatrixCoherence
  complexPhaseRetained :
    FiniteBranchDecision complexTriadPhaseCoherence
  triadDirectionPromoted :
    FiniteBranchDecision triadDirectionCoherence

globalBranchDecision : FiniteBranchDecision globalHelicity
globalBranchDecision = globalRejected

scalarLocalizedBranchDecision :
  FiniteBranchDecision scalarLocalizedHelicity
scalarLocalizedBranchDecision = scalarLocalizedRejected

projectedAxisBranchDecision :
  FiniteBranchDecision projectedAxisMatrixCoherence
projectedAxisBranchDecision = projectedAxisRejectedOnOptimizedSupport

complexTriadPhaseBranchDecision :
  FiniteBranchDecision complexTriadPhaseCoherence
complexTriadPhaseBranchDecision = complexPhaseRetained

triadDirectionBranchDecision :
  FiniteBranchDecision triadDirectionCoherence
triadDirectionBranchDecision = triadDirectionPromoted

record FiniteDecisionReceipt : Set where
  constructor decision-receipt
  field
    globalReceipt : Global.GlobalHelicityCounterexampleReceipt
    localizedReceipt : Local.LocalizedHelicityExactReceipt
    balancedReceipt : Balanced.BalancedFamilyExactReceipt
    phaseEvidence : Phase.PhaseFallbackFiniteEvidence
    matrixReceipt : Matrix.MatrixCoherenceReconnaissanceReceipt
    directionDiagnostic : Direction.FourierPolarizationGramDiagnostic

open FiniteDecisionReceipt public

finiteDecisionReceipt : FiniteDecisionReceipt
finiteDecisionReceipt =
  decision-receipt
    Global.globalHelicityH3Counterexample
    Local.localizedHelicityExactReceipt
    Balanced.balancedFamilyExactReceipt
    Phase.phaseFallbackFiniteEvidence
    Matrix.matrixCoherenceReconnaissanceReceipt
    Direction.exactPolarizationDiagnostic

record DirectionCoherenceResearchCutset
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff State Scalar : Set c
    SelectedFunctional : State → Scalar

    physicalDirectionKernelIdentified : Set s
    triadDirectionKernelIdentified : Set s
    translationEquivariantFunctionalConstructed : Set s
    functionalDegreeAccountingClosed : Set s
    selectedFunctionalCoercive : Set s
    literalGalerkinChainRuleClosed : Set s
    cutoffUniformHarmonicAnalysisClosed : Set s
    signedMixedHelicityClassesClosed : Set s
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

open DirectionCoherenceResearchCutset public

permanav3RouteConsumedAsTheorem :
  Permana.ClaimStatus
permanav3RouteConsumedAsTheorem = Permana.unverified
