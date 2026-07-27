module DASHI.Physics.Closure.NSTriadKNHelicalCandidateDecisionFork where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact helical, coherence, and Stage-3 analytic closure decision fork".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original dependency theorem.
-- Uses: finite coherence falsifications, Kiriukhin row/symmetric theorems,
-- Grafakos--Torres transpose and three-function frameworks, Tao/Bony
-- trichotomy, Bernstein auditing, exact derivative/Leray placement, and the
-- asymmetric high-high-to-low audit.
-- Relationship: the scalar transpose symbols are exact. Output freezing gets
-- incompressibility relocation and the second adjoint differentiates its
-- frozen leg, while the first adjoint has an exact counterexample to a
-- primitive low-frequency derivative gain. Its tail/commutator ledger remains
-- the principal Stage-3 analytic leaf.
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
import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao
import DASHI.Physics.Closure.NSTriadKNBernsteinDirectionAudit as Bernstein
import DASHI.Physics.Closure.NSTriadKNGrafakosTorresExactTransposeSymbols as Transpose
import DASHI.Physics.Closure.NSTriadKNFrozenLegDerivativeLerayLedger as Derivative
import DASHI.Physics.Closure.NSTriadKNShellExponentLedgerProgram as Ledgers
import DASHI.Physics.Closure.NSTriadKNHighHighToLowCancellationProgram as HighHigh
import DASHI.Physics.Closure.NSTriadKNThreeWeightAffineCertificateProgram as Certificate
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
  complexPhaseRetained : FiniteBranchDecision complexTriadPhaseCoherence
  triadDirectionPromoted : FiniteBranchDecision triadDirectionCoherence

globalBranchDecision : FiniteBranchDecision globalHelicity
globalBranchDecision = globalRejected

scalarLocalizedBranchDecision : FiniteBranchDecision scalarLocalizedHelicity
scalarLocalizedBranchDecision = scalarLocalizedRejected

projectedAxisBranchDecision :
  FiniteBranchDecision projectedAxisMatrixCoherence
projectedAxisBranchDecision = projectedAxisRejectedOnOptimizedSupport

complexTriadPhaseBranchDecision :
  FiniteBranchDecision complexTriadPhaseCoherence
complexTriadPhaseBranchDecision = complexPhaseRetained

triadDirectionBranchDecision : FiniteBranchDecision triadDirectionCoherence
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
  exactTransposeSymbols
  frozenOutputTwoFunction
  frozenLegParametrizedTrichotomy
  asymmetricHighHighCancellation
  exactAffineCertificate
  paraproductPartialAdjoints : HarmonicRoute

data HarmonicRouteDecision : HarmonicRoute → Set where
  rawRowLiteratureBacked : HarmonicRouteDecision rawOrbitRow
  symmetricStretchingRetainedForContinuation :
    HarmonicRouteDecision symmetricOrbitStretching
  threeFunctionPromotedAsPrimary :
    HarmonicRouteDecision grafakosTorresThreeFunction
  scalarTransposeSymbolsPromotedAsExact :
    HarmonicRouteDecision exactTransposeSymbols
  twoFunctionRetainedAsSpecialization :
    HarmonicRouteDecision frozenOutputTwoFunction
  frozenLegTrichotomyRetainedForSharedCombinatorics :
    HarmonicRouteDecision frozenLegParametrizedTrichotomy
  asymmetricHighHighAuditRetained :
    HarmonicRouteDecision asymmetricHighHighCancellation
  affineCertificateRetainedFailClosed :
    HarmonicRouteDecision exactAffineCertificate
  paraproductPartialAdjointsRetained :
    HarmonicRouteDecision paraproductPartialAdjoints

rawOrbitRowDecision : HarmonicRouteDecision rawOrbitRow
rawOrbitRowDecision = rawRowLiteratureBacked

symmetricStretchingDecision : HarmonicRouteDecision symmetricOrbitStretching
symmetricStretchingDecision = symmetricStretchingRetainedForContinuation

threeFunctionDecision : HarmonicRouteDecision grafakosTorresThreeFunction
threeFunctionDecision = threeFunctionPromotedAsPrimary

exactTransposeDecision : HarmonicRouteDecision exactTransposeSymbols
exactTransposeDecision = scalarTransposeSymbolsPromotedAsExact

twoFunctionSpecializationDecision :
  HarmonicRouteDecision frozenOutputTwoFunction
twoFunctionSpecializationDecision = twoFunctionRetainedAsSpecialization

frozenLegTrichotomyDecision :
  HarmonicRouteDecision frozenLegParametrizedTrichotomy
frozenLegTrichotomyDecision =
  frozenLegTrichotomyRetainedForSharedCombinatorics

asymmetricHighHighDecision :
  HarmonicRouteDecision asymmetricHighHighCancellation
asymmetricHighHighDecision = asymmetricHighHighAuditRetained

affineCertificateDecision : HarmonicRouteDecision exactAffineCertificate
affineCertificateDecision = affineCertificateRetainedFailClosed

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

    taoFrozenLegTrichotomyAvailable :
      Stage3Schur.taoFrozenLegTrichotomyRepresented ≡ true
    frozenLegPermutationDoesNotCloseAdjoints :
      Stage3Schur.frozenLegPermutationClosesPartialAdjoints ≡ false
    bernsteinDirectionAuditAvailable :
      Stage3Schur.bernsteinDirectionAuditRepresented ≡ true
    bernsteinDoesNotSupplyLowFrequencyDecay :
      Stage3Schur.bernsteinAloneSuppliesLowFrequencyDecay ≡ false

    scalarTransposeSymbolsExact :
      Stage3Schur.literalScalarTransposeSymbolsClosed ≡ true
    vectorTransposeFormulasRemainOpen :
      Stage3Schur.literalVectorTransposeFormulasClosed ≡ false
    germainAttributionCorrected :
      Stage3Schur.germainEightClassAttributionCorrected ≡ true

    outputStructuralGainAvailable :
      Stage3Schur.outputHighHighStructuralGainIdentified ≡ true
    firstAdjointPrimitiveGainUnavailable :
      Stage3Schur.firstAdjointPrimitiveLowGainAvailable ≡ false
    secondAdjointStructuralLowDerivativeAvailable :
      Stage3Schur.secondAdjointStructuralLowDerivativeIdentified ≡ true

    rowOnlyDoesNotDetermineThreeWeights :
      Stage3Schur.kiriukhinRowAloneDeterminesTriadicWeights ≡ false
    strictCertificateStillOpen :
      Stage3Schur.strictThreeWeightCertificateClosed ≡ false

    symmetricRankAudit : Symmetric.SymmetricCompanionRankAudit
    kernelPermutationReceipt : Transpose.KernelPermutationReceipt
    frozenTransposeReceipt : Transpose.FrozenOperatorTransposeReceipt
    frozenLegReceipt : Tao.FrozenLegPermutationReceipt
    derivativeReceipt : Derivative.FrozenLegDerivativeReceipt
    gainReceipt : HighHigh.FrozenLegGainReceipt
    attributionReceipt : Ledgers.AttributionReceipt
    readinessReceipt : Certificate.AnalyticReadinessReceipt
    bernsteinReceipt : Bernstein.BernsteinDirectionReceipt
    sourceExponentReceipt : Exponents.GrafakosTorresSourceExponentReceipt
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
    Stage3Schur.taoFrozenLegTrichotomyRepresentedIsTrue
    Stage3Schur.frozenLegPermutationClosesPartialAdjointsIsFalse
    Stage3Schur.bernsteinDirectionAuditRepresentedIsTrue
    Stage3Schur.bernsteinAloneSuppliesLowFrequencyDecayIsFalse
    Stage3Schur.literalScalarTransposeSymbolsClosedIsTrue
    Stage3Schur.literalVectorTransposeFormulasClosedIsFalse
    Stage3Schur.germainEightClassAttributionCorrectedIsTrue
    Stage3Schur.outputHighHighStructuralGainIdentifiedIsTrue
    Stage3Schur.firstAdjointPrimitiveLowGainAvailableIsFalse
    Stage3Schur.secondAdjointStructuralLowDerivativeIdentifiedIsTrue
    Stage3Schur.kiriukhinRowAloneDeterminesTriadicWeightsIsFalse
    Stage3Schur.strictThreeWeightCertificateClosedIsFalse
    Symmetric.symmetricCompanionRankAudit
    Transpose.kernelPermutationReceipt
    Transpose.frozenOperatorTransposeReceipt
    Tao.frozenLegPermutationReceipt
    Derivative.frozenLegDerivativeReceipt
    HighHigh.frozenLegGainReceipt
    Ledgers.attributionReceipt
    Certificate.analyticReadinessReceipt
    Bernstein.bernsteinDirectionReceipt
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

    exactScalarTransposeSymbolsClosed : Set s
    exactVectorTransposeSymbolsClosed : Set s
    frozenLegParametrizedTrichotomyClosed : Set s
    frozenLegClassPermutationClosed : Set s
    bernsteinDirectionsConsumed : Set s
    lowPassDecayNotInferredFromBernsteinAlone : Set s

    outputDerivativeAndLerayPlacementClosed : Set s
    firstAdjointDerivativeAndLerayPlacementClosed : Set s
    secondAdjointDerivativeAndLerayPlacementClosed : Set s

    outputHighHighGainClosed : Set s
    firstAdjointTailOrCommutatorGainClosed : Set s
    secondAdjointDirectLowDerivativeClosed : Set s

    outputRowHomogeneityExtracted : Set s
    firstPartialAdjointHomogeneityExtracted : Set s
    secondPartialAdjointHomogeneityExtracted : Set s
    threeLegAffineExponentSystemSolved : Set s
    strictEpsilonCertificateClosed : Set s
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

permanav3RouteConsumedAsTheorem : Permana.ClaimStatus
permanav3RouteConsumedAsTheorem = Permana.unverified
