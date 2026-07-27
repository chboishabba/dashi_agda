module DASHI.Physics.Closure.NSTriadKNHelicalCandidateDecisionFork where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact helical, coherence, and Stage-3 harmonic-analysis decision
-- fork with remaining analytic cutset".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original dependency theorem.
-- Uses: the global/scalar-helicity counterexamples, projected-axis matrix
-- reconnaissance, Constantin--Fefferman direction-coherence interface,
-- triad-direction diagnostics, Kiriukhin raw-row theorem, weighted Schur,
-- multilinear Schur, paraproduct duality, and the fail-closed Permana audit.
-- Relationship: keeps candidate-selection decisions separate from harmonic
-- strategy decisions. It rejects only the concretely tested projected-axis
-- mode-local family, promotes triad direction coherence, records the raw row
-- theorem as literature-backed, and leaves every adapter, weighted column,
-- dual-trilinear, and cutoff-uniform PDE estimate explicit and uninhabited.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGlobalHelicityH3DiscriminantCounterexample as Global
import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityExactReconnaissance as Local
import DASHI.Physics.Closure.NSTriadKNFixedSymbolBalancedFamilyReconnaissance as Balanced
import DASHI.Physics.Closure.NSTriadKNTriadPhaseCoherenceFallback as Phase
import DASHI.Physics.Closure.NSTriadKNMatrixCoherenceExactReconnaissance as Matrix
import DASHI.Physics.Closure.NSTriadKNTriadDirectionAlignmentProgram as Direction
import DASHI.Physics.Closure.NSTriadKNPermanaAlignmentRateAudit as Permana
import DASHI.Physics.Closure.NSTriadKNKiriukhinWeightedSchurFiniteReconnaissance as SchurFinite
import DASHI.Physics.Closure.NSTriadKNStage3KiriukhinWeightedSchurProgram as Stage3Schur

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

data HarmonicRoute : Set where
  rawOrbitRow
  twoFunctionWeightedSchur
  multilinearDualTrilinear : HarmonicRoute

data HarmonicRouteDecision : HarmonicRoute → Set where
  rawRowLiteratureBacked : HarmonicRouteDecision rawOrbitRow
  weightedSchurPromoted : HarmonicRouteDecision twoFunctionWeightedSchur
  multilinearDualityRetained : HarmonicRouteDecision multilinearDualTrilinear

rawOrbitRowDecision : HarmonicRouteDecision rawOrbitRow
rawOrbitRowDecision = rawRowLiteratureBacked

twoFunctionWeightedSchurDecision :
  HarmonicRouteDecision twoFunctionWeightedSchur
twoFunctionWeightedSchurDecision = weightedSchurPromoted

multilinearDualTrilinearDecision :
  HarmonicRouteDecision multilinearDualTrilinear
multilinearDualTrilinearDecision = multilinearDualityRetained

record Stage3DecisionReceipt : Set where
  constructor stage3-decision-receipt
  field
    rawRowSourceAvailable :
      Stage3Schur.kiriukhinRawRowLiteratureBacked ≡ true
    finiteWeightEvidence : SchurFinite.WeightedSchurFiniteReceipt

open Stage3DecisionReceipt public

stage3DecisionReceipt : Stage3DecisionReceipt
stage3DecisionReceipt =
  stage3-decision-receipt
    Stage3Schur.kiriukhinRawRowLiteratureBackedIsTrue
    SchurFinite.weightedSchurFiniteReceipt

record DirectionCoherenceResearchCutset
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff State : Set c
    Scalar : Set s
    SelectedFunctional : State → Scalar

    kiriukhinRawKernelIdentified : Set s
    kiriukhinConventionAdapterClosed : Set s
    orbitToDyadicShellBridgeClosed : Set s
    finiteHelicityRowLiftClosed : Set s
    boundedDirectionWeightRowLiftClosed : Set s
    baselineWeightedColumnClosed : Set s
    multilinearPartialAdjointsClosed : Set s
    cutoffUniformDualTrilinearBoundClosed : Set s

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
