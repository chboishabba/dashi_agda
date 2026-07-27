module DASHI.Physics.Closure.NSTriadKNHelicalCandidateDecisionFork where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact helical, coherence, and Stage-3 three-function harmonic
-- analysis decision fork with symmetric-companion rank audit".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original dependency theorem.
-- Uses: the global/scalar-helicity counterexamples, projected-axis matrix
-- reconnaissance, Constantin--Fefferman direction-coherence interface,
-- triad-direction diagnostics, Kiriukhin raw-row and symmetric-stretching
-- theorems, Grafakos--Torres three-function Schur, the frozen-output linear
-- specialization, paraproduct partial adjoints, and the fail-closed Permana
-- audit.
-- Relationship: keeps candidate-selection decisions separate from harmonic
-- strategy decisions.  The raw row theorem supplies one output-side condition.
-- The symmetric companion controls orbit-level enstrophy growth but adds no
-- independent raw partial-adjoint exponent equation, so both adjoints remain
-- open.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNGlobalHelicityH3DiscriminantCounterexample as Global
import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityExactReconnaissance as Local
import DASHI.Physics.Closure.NSTriadKNFixedSymbolBalancedFamilyReconnaissance as Balanced
import DASHI.Physics.Closure.NSTriadKNTriadPhaseCoherenceFallback as Phase
import DASHI.Physics.Closure.NSTriadKNMatrixCoherenceExactReconnaissance as Matrix
import DASHI.Physics.Closure.NSTriadKNTriadDirectionAlignmentProgram as Direction
import DASHI.Physics.Closure.NSTriadKNPermanaAlignmentRateAudit as Permana
import DASHI.Physics.Closure.NSTriadKNKiriukhinWeightedSchurFiniteReconnaissance as SchurFinite
import DASHI.Physics.Closure.NSTriadKNKiriukhinSymmetricStretchingCompanionAudit as Symmetric
import DASHI.Physics.Closure.NSTriadKNTriadicDyadicExponentSystem as Exponents
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
  symmetricOrbitStretching
  grafakosTorresThreeFunction
  frozenOutputTwoFunction
  paraproductPartialAdjoints : HarmonicRoute

data HarmonicRouteDecision : HarmonicRoute → Set where
  rawRowLiteratureBacked : HarmonicRouteDecision rawOrbitRow
  symmetricStretchingRetainedForContinuation :
    HarmonicRouteDecision symmetricOrbitStretching
  threeFunctionPromotedAsPrimary :
    HarmonicRouteDecision grafakosTorresThreeFunction
  twoFunctionRetainedAsSpecialization :
    HarmonicRouteDecision frozenOutputTwoFunction
  paraproductPartialAdjointsRetained :
    HarmonicRouteDecision paraproductPartialAdjoints

rawOrbitRowDecision : HarmonicRouteDecision rawOrbitRow
rawOrbitRowDecision = rawRowLiteratureBacked

symmetricStretchingDecision :
  HarmonicRouteDecision symmetricOrbitStretching
symmetricStretchingDecision = symmetricStretchingRetainedForContinuation

threeFunctionDecision :
  HarmonicRouteDecision grafakosTorresThreeFunction
threeFunctionDecision = threeFunctionPromotedAsPrimary

twoFunctionSpecializationDecision :
  HarmonicRouteDecision frozenOutputTwoFunction
twoFunctionSpecializationDecision = twoFunctionRetainedAsSpecialization

paraproductPartialAdjointDecision :
  HarmonicRouteDecision paraproductPartialAdjoints
paraproductPartialAdjointDecision = paraproductPartialAdjointsRetained

record Stage3DecisionReceipt : Set where
  constructor stage3-decision-receipt
  field
    rawRowSourceAvailable :
      Stage3Schur.kiriukhinRawRowLiteratureBacked ≡ true
    symmetricStretchingSourceAvailable :
      Stage3Schur.kiriukhinSymmetricStretchingLiteratureBacked ≡ true
    symmetricCompanionDoesNotReduceNullity :
      Stage3Schur.symmetricCompanionReducesTriadicNullity ≡ false
    threeFunctionFrameworkPrimary :
      Stage3Schur.threeFunctionSchurPrimary ≡ true
    twoFunctionIsSpecialization :
      Stage3Schur.twoFunctionSchurIsFrozenOutputSpecialization ≡ true
    rowOnlyDoesNotDetermineThreeWeights :
      Stage3Schur.kiriukhinRowAloneDeterminesTriadicWeights ≡ false
    symmetricRankAudit : Symmetric.SymmetricCompanionRankAudit
    sourceExponentReceipt :
      Exponents.GrafakosTorresSourceExponentReceipt
    finiteWeightEvidence : SchurFinite.WeightedSchurFiniteReceipt

open Stage3DecisionReceipt public

stage3DecisionReceipt : Stage3DecisionReceipt
stage3DecisionReceipt =
  stage3-decision-receipt
    Stage3Schur.kiriukhinRawRowLiteratureBackedIsTrue
    Stage3Schur.kiriukhinSymmetricStretchingLiteratureBackedIsTrue
    Stage3Schur.symmetricCompanionReducesTriadicNullityIsFalse
    Stage3Schur.threeFunctionSchurPrimaryIsTrue
    Stage3Schur.twoFunctionSchurIsFrozenOutputSpecializationIsTrue
    Stage3Schur.kiriukhinRowAloneDeterminesTriadicWeightsIsFalse
    Symmetric.symmetricCompanionRankAudit
    Exponents.grafakosTorresSourceExponentReceipt
    SchurFinite.weightedSchurFiniteReceipt

record DirectionCoherenceResearchCutset
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff State : Set c
    Scalar : Set s
    SelectedFunctional : State → Scalar

    kiriukhinRawKernelIdentified : Set s
    kiriukhinConventionAdapterClosed : Set s
    symmetricStretchingAdapterClosed : Set s
    symmetricContinuationBridgeClosed : Set s
    orbitToDyadicShellBridgeClosed : Set s
    finiteHelicityRowLiftClosed : Set s
    boundedDirectionWeightRowLiftClosed : Set s

    outputRowHomogeneityExtracted : Set s
    firstPartialAdjointHomogeneityExtracted : Set s
    secondPartialAdjointHomogeneityExtracted : Set s
    threeLegAffineExponentSystemSolved : Set s
    repositorySeparationThresholdDerived : Set s

    grafakosTorresOutputConditionClosed : Set s
    grafakosTorresFirstAdjointConditionClosed : Set s
    grafakosTorresSecondAdjointConditionClosed : Set s
    cutoffUniformThreeFunctionBoundClosed : Set s

    frozenOutputTwoFunctionFallbackClosed : Set s
    paraproductClasswisePartialAdjointsClosed : Set s

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
