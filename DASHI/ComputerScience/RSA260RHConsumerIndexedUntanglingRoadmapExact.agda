module DASHI.ComputerScience.RSA260RHConsumerIndexedUntanglingRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Localization
import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA
import DASHI.ComputerScience.RSA260BidiRankObserverGrowthStressExact as RankGrowth
import DASHI.ComputerScience.RSA260BidiMksolConsumerProjectionExact as MksolProjection
import DASHI.ComputerScience.RSA260BidiMksolStyleConsumerCollisionExact as MksolCollision
import DASHI.ComputerScience.RSA260BidiHybridReplayMksolAdequacyExact as ReplayAdequacy
import DASHI.ComputerScience.RSA260BidiMksolActionKernelQuotientExact as ActionKernel
import DASHI.ComputerScience.RSA260BidiMksolVContextStressExact as VStress
import DASHI.ComputerScience.RSA260BidiCADOMksolContextFamilyExact as CADOFamily
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as RHWeld
import DASHI.Analysis.RiemannG2PhaseWeldCellwiseUpperBridgeExact as RHUpper
import DASHI.Analysis.RiemannG2PhaseSensitiveRuntimeDiagnosticExact as RHRuntime
import DASHI.Analysis.RiemannG2PhaseSensitiveRuntimeStressExact as RHStress
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production

------------------------------------------------------------------------
-- RSA-260 / RH CONSUMER-INDEXED UNTANGLING ROADMAP
--
-- INFORMATION DESCENT
--   candidate quotient -> consumer collision -> localize missing information ->
--   retain only the smallest coordinate family adequate for the DECLARED
--   consumer family -> stress by broadening that family.
--
-- SEMANTIC ASCENT
--   localized coordinate -> same-object realization -> weakest theorem/estimate
--   sufficient for the DECLARED downstream consumer -> aggregate consumer.
------------------------------------------------------------------------

coreTowerBoundary : Tower.ConsumerIndexedUntanglingTowerBoundary
coreTowerBoundary = Tower.canonicalConsumerIndexedUntanglingTowerBoundary

coreLocalizationBoundary : Localization.ConsumerIndexedResidualLocalizationBoundary
coreLocalizationBoundary = Localization.canonicalConsumerIndexedResidualLocalizationBoundary

rsaTowerBoundary : RSA.RSAConsumerIndexedUntanglingBoundary
rsaTowerBoundary = RSA.canonicalRSAConsumerIndexedUntanglingBoundary

rankGrowthBoundary : RankGrowth.RankObserverGrowthStressBoundary
rankGrowthBoundary = RankGrowth.canonicalRankObserverGrowthStressBoundary

mksolProjectionBoundary : MksolProjection.MksolConsumerProjectionBoundary
mksolProjectionBoundary = MksolProjection.canonicalMksolConsumerProjectionBoundary

mksolCollisionBoundary : MksolCollision.MksolStyleConsumerCollisionBoundary
mksolCollisionBoundary = MksolCollision.canonicalMksolStyleConsumerCollisionBoundary

replayAdequacyBoundary : ReplayAdequacy.HybridReplayMksolAdequacyBoundary
replayAdequacyBoundary = ReplayAdequacy.canonicalHybridReplayMksolAdequacyBoundary

actionKernelBoundary : ActionKernel.MksolActionKernelQuotientBoundary
actionKernelBoundary = ActionKernel.canonicalMksolActionKernelQuotientBoundary

vStressBoundary : VStress.MksolVContextStressBoundary
vStressBoundary = VStress.canonicalMksolVContextStressBoundary

cadoFamilyBoundary : CADOFamily.CADOMksolContextFamilyBoundary
cadoFamilyBoundary = CADOFamily.canonicalCADOMksolContextFamilyBoundary

rhTowerBoundary : RH.RHConsumerIndexedUntanglingBoundary
rhTowerBoundary = RH.canonicalRHConsumerIndexedUntanglingBoundary

rhWeldBoundary : RHWeld.LiteralPhaseModulationWeldBoundary
rhWeldBoundary = RHWeld.canonicalLiteralPhaseModulationWeldBoundary

rhUpperBoundary : RHUpper.PhaseWeldCellwiseUpperBridgeBoundary
rhUpperBoundary = RHUpper.canonicalPhaseWeldCellwiseUpperBridgeBoundary

rhRuntimeBoundary : RHRuntime.PhaseSensitiveRuntimeDiagnosticBoundary
rhRuntimeBoundary = RHRuntime.canonicalPhaseSensitiveRuntimeDiagnosticBoundary

rhStressBoundary : RHStress.PhaseSensitiveRuntimeStressBoundary
rhStressBoundary = RHStress.canonicalPhaseSensitiveRuntimeStressBoundary

productionFirstResidual : Production.ProductionResidual
productionFirstResidual = Production.firstUnpaidProductionResidual

------------------------------------------------------------------------
-- RSA research queue.
--
-- Rank fingerprints fail a concrete generator-action consumer. Exact replay is
-- a sufficient upper endpoint. A fixed synthetic V can expose an action-kernel
-- quotient, but a second V can reopen that kernel completely. Therefore any
-- useful compression must preserve the whole DECLARED source-native mksol family.
--
-- Published RSA-260 coordinates now retained:
--   * two width-256 Krylov sequences;
--   * 40 mksol ranges of width 32768.
-- Exact V-file/range binding and prepared-operator identity remain unpaid.
------------------------------------------------------------------------

data ResearchUntanglingTarget : Set where
  bindPublishedSequencesToExactRSA260VFiles : ResearchUntanglingTarget
  bindPublishedMksolRangesToExactSolutionFiles : ResearchUntanglingTarget
  bindPreparedOperatorSameObjectIdentity : ResearchUntanglingTarget
  instantiateDeclaredProductionMksolContextFamily : ResearchUntanglingTarget
  testActionKernelIntersectionAcrossDeclaredContextFamily : ResearchUntanglingTarget
  searchOnlyPersistentEvaluationKernelForCompression : ResearchUntanglingTarget
  retainExactReplayAsSufficientUpperEndpoint : ResearchUntanglingTarget
  retainRanksOnlyAsCheapDiagnostics : ResearchUntanglingTarget

firstResearchUntanglingTarget : ResearchUntanglingTarget
firstResearchUntanglingTarget = bindPublishedSequencesToExactRSA260VFiles

------------------------------------------------------------------------
-- Production queue.
------------------------------------------------------------------------

data ProductionReconstructionTarget : Set where
  acquireSameObjectFineIncidenceBearingLACarrier : ProductionReconstructionTarget
  authenticateSameObjectBalancingAndPreparation : ProductionReconstructionTarget
  executeIndependentKrylovProjection : ProductionReconstructionTarget
  recoverIndependentGeneratorResidual : ProductionReconstructionTarget
  bindSameObjectInitialVAndMksolContextFamily : ProductionReconstructionTarget
  replayIndependentMksol : ProductionReconstructionTarget
  verifyIndependentNonzeroKernel : ProductionReconstructionTarget
  compileFactorCertificate : ProductionReconstructionTarget

firstProductionReconstructionTarget : ProductionReconstructionTarget
firstProductionReconstructionTarget = acquireSameObjectFineIncidenceBearingLACarrier

------------------------------------------------------------------------
-- RH analytic queue.
--
-- Runtime diagnostics now cover 18 initial cells and a 72-case stress family
-- over multiple target zeros, Gaussian widths and horizontal displacements.
-- Every tested one-sided phase-sensitive upper held; the broader stress ratio
-- phaseUpper/coarseUpper ranged approximately 0.318..0.906 with median 0.373.
--
-- This still uses diagnostic Gaussian tapers. Repository source names the final
-- literal carrier as 4*g_pole*cosh(a*u)*cos(delta*u) but keeps g_pole abstract;
-- it explicitly rejects silently substituting the rank-two determinant taper.
------------------------------------------------------------------------

data RHAnalyticRefinementTarget : Set where
  obtainConcreteFinalUniversalPoleQuotientTaperEvaluation : RHAnalyticRefinementTarget
  inhabitUniversalPoleQuotientPhaseModulationWeld : RHAnalyticRefinementTarget
  constructProofCarryingPhaseSensitivePointwiseMajorant : RHAnalyticRefinementTarget
  provePairSpecificIntegralMonotonicity : RHAnalyticRefinementTarget
  certifyIntegratedMajorantCellUppers : RHAnalyticRefinementTarget
  instantiateExactFiniteNearEnumeration : RHAnalyticRefinementTarget
  compileOneSidedFinalNearUpper : RHAnalyticRefinementTarget
  payStrictNearComplementConsumerMargin : RHAnalyticRefinementTarget
  optionalProveExactAggregationCongruence : RHAnalyticRefinementTarget
  closeOnlyThenPromoteRHTerminal : RHAnalyticRefinementTarget

firstRHAnalyticRefinementTarget : RHAnalyticRefinementTarget
firstRHAnalyticRefinementTarget = obtainConcreteFinalUniversalPoleQuotientTaperEvaluation

record RSA260RHUntanglingRoadmapBoundary : Set where
  constructor rsa260-rh-untangling-roadmap-boundary
  field
    genericConsumerIndexedTowerPaid : Bool
    genericResidualLocalizationPaid : Bool

    rankFingerprintsRemainUsefulDiagnostics : Bool
    rankFingerprintPaysSyntheticMksolActionConsumer : Bool
    concreteMksolStyleRankCollisionPaid : Bool
    exactReplayPreservesPureGeneratorConsumers : Bool
    fixedContextActionKernelObserved : Bool
    fixedContextKernelStableUnderCheckedSecondV : Bool
    checkedTwoVFamilyReopensFullDegree17CoefficientSpace : Bool
    sourceNativeMksolContextFamilyInterfacePaid : Bool
    publishedTwoWidth256SequencesRetained : Bool
    publishedFortyRangesOf32768Retained : Bool
    exactRSA260VFileBindingPaid : Bool
    exactRSA260RangeFileBindingPaid : Bool
    exactPreparedOperatorIdentityPaid : Bool

    rhFinitePhaseLocalized : Bool
    rhLiteralPhaseWeldInterfaceWritten : Bool
    rhOneSidedCellUpperBridgeWritten : Bool
    rhInitialPythonDiagnosticExecuted : Bool
    rhBroaderSeventyTwoCaseStressExecuted : Bool
    rhAllSeventyTwoStressBoundsHeld : Bool
    rhPythonUsesFinalUniversalPoleQuotientTaper : Bool
    concreteFinalPoleQuotientTaperEvaluationOwned : Bool
    rhPhaseSensitiveMajorantAuthorityPaid : Bool
    rhActualUniversalPoleQuotientWeldPaid : Bool
    rhStrictNearComplementMarginPaid : Bool
    exactAggregationCongruenceRequiredForCurrentUpperConsumer : Bool

    productionSearchForUnpublishedIntermediateBytesRequired : Bool
    productionSubstitutionReturnsToFineIncidenceMatrixCarrier : Bool
    independentArtifactsAreHistoricalWithheldArtifacts : Bool

    adequacyMustPrecedeParetoRanking : Bool
    consumerFamilyMustPrecedeCompressionRanking : Bool
    weakerConsumerSufficientRoutePreferredWhenAvailable : Bool
    threeQueuesMayAdvanceIndependently : Bool
open RSA260RHUntanglingRoadmapBoundary public

canonicalRSA260RHUntanglingRoadmapBoundary :
  RSA260RHUntanglingRoadmapBoundary
canonicalRSA260RHUntanglingRoadmapBoundary =
  rsa260-rh-untangling-roadmap-boundary
    true true
    true false true true true false true true true false false false false
    true true true true true true false false false false false false
    false true false
    true true true true
