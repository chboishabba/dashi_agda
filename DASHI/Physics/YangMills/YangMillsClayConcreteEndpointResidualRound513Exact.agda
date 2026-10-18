{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayConcreteEndpointResidualRound513Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND513: RESIDUAL AFTER CONCRETE ENDPOINT SEMANTICS
--
-- R509 removes A3 finite-family convergence from hard analysis.
-- R511 gives source-backed meanings to the represented continuum / OS /
-- spectral-gap / nontriviality endpoint predicates.
-- R512 chooses the terminal literal objects directly from those sources.
--
-- Therefore twelve former endpoint-semantic leaves are compiler-owned:
--
--   A3: continuum limit, Schwinger belongs;
--   T3: accepted OS, reconstructed Hilbert, positive self-adjoint H;
--   B:  vacuum/positive-energy, strict gap, physical lower scale,
--       no spectral pollution, gap+clustering derived;
--   G2: literal nontriviality, nontriviality preserved in limit.
--
-- No new physical theorem is introduced by this recut.  The proof-bearing
-- source bundle is supplied by the already-visible A3/B/OS/G source lanes.
--
-- New exhaustive residual:
--
--   17 source-analysis
--   18 source<->literal attachment
--   21 endpoint-semantics (exactly structural/T1/T4)
--   ------------------------------------------------
--   56 total
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
import DASHI.Physics.YangMills.YangMillsRepresentedExpectationConvergenceRound509Exact as R509
import DASHI.Physics.YangMills.YangMillsConcreteEndpointSemanticsRound511Exact as R511
import DASHI.Physics.YangMills.YangMillsConcreteEndpointConstructionRound512Exact as R512

sourceAnalysisLeaves : List R496.ResidualLeaf
sourceAnalysisLeaves =
    R496.a1WilsonHessianVariation
  ∷ R496.a1AveragingConstraintVariation
  ∷ R496.a1GaugeProjectionVariation
  ∷ R496.a1WQRAssembly
  ∷ R496.a1ConstrainedGaussianMixedCoefficient
  ∷ R496.a1PhysicalJetFiveChannelSplit
  ∷ R496.a1FourJointReceiptEvaluation
  ∷ R496.a3ProjectiveEventExpectationConsistency
  ∷ R496.a3ContinuityAtEmpty
  ∷ R496.a4FiniteRegularityFromQuantitativeBounds
  ∷ R496.a5FiniteGrowthFromQuantitativeBounds
  ∷ R496.bWilsonTwoMarkExpansion
  ∷ R496.bWilsonConnectingWeightTail
  ∷ R496.bSameHamiltonianTransferCoordinate
  ∷ R496.c1MarkedSourceHilbertModulus
  ∷ R496.c4LiteralDensityMetricDerivative
  ∷ R496.g1ArbitraryCompactSimpleSourceMap
  ∷ []

sourceLiteralAttachmentLeaves : List R496.ResidualLeaf
sourceLiteralAttachmentLeaves =
    R496.aFiniteEuclideanSameObjectAttachment
  ∷ R496.aFiniteBosonicSameObjectAttachment
  ∷ R496.aFiniteWilsonRPSameObjectAttachment
  ∷ R496.a2BetaMarkGeneratedHistoryShell
  ∷ R496.a3StressDensityIsLiteralFiniteMeasure
  ∷ R496.a3SourceOSIsLiteralSchwinger
  ∷ R496.a3CylinderEventIndicatorSemantics
  ∷ R496.a3CylinderExpectationIntegralIdentification
  ∷ R496.a45QuantitativeFiniteExpectationAttachment
  ∷ R496.a4RepresentedRegularityExtensionality
  ∷ R496.a5RepresentedGrowthExtensionality
  ∷ R496.c1CurvatureGaugeLocalSemantics
  ∷ R496.c2PhysicalRemainderIsCompositeTail
  ∷ R496.c3OneStepAFRGIdentification
  ∷ R496.c4FiniteStressInsertionIsCMP119Local
  ∷ R496.c4StressCompletionIsCompletedMarkedStress
  ∷ R496.c4CompletedStressIsClayStress
  ∷ R496.c4DensityAnchoredLaneInstantiation
  ∷ []

endpointSemanticLeaves : List R496.ResidualLeaf
endpointSemanticLeaves =
    R496.structuralCompactSimpleSemantics
  ∷ R496.structuralFourDimensionalEuclideanSemantics
  ∷ R496.structuralCompactSimpleParameterizationSemantics
  ∷ R496.t1FiniteVolumeCutoffMeasureSemantics
  ∷ R496.t1ReflectionPositiveRegularizationSemantics
  ∷ R496.t1UltravioletNormalizationSemantics
  ∷ R496.t1AsymptoticallyFreeTrajectorySemantics
  ∷ R496.t1GaugeSymmetryPreservedSemantics
  ∷ R496.t1LocalityPreservedSemantics
  ∷ R496.t1EuclideanCovariancePreservedSemantics
  ∷ R496.t1ReflectionPositivityPreservedSemantics
  ∷ R496.t1PositivityNormalizationPreservedSemantics
  ∷ R496.t1VolumeCutoffCompatibilitySemantics
  ∷ R496.t4GaugeInvariantLocalObservableSemantics
  ∷ R496.t4CurvatureCorrespondenceSemantics
  ∷ R496.t4CurvatureGaugeInvariantSemantics
  ∷ R496.t4CurvatureLocalitySemantics
  ∷ R496.t4ShortDistanceAFSemantics
  ∷ R496.t4StressTensorAndOPESemantics
  ∷ R496.t4PhysicalOPECoefficientSemantics
  ∷ R496.t4PhysicalOPERemainderSemantics
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

sourceAnalysisLeafCount : Nat
sourceAnalysisLeafCount = listLength sourceAnalysisLeaves

sourceLiteralAttachmentLeafCount : Nat
sourceLiteralAttachmentLeafCount = listLength sourceLiteralAttachmentLeaves

endpointSemanticLeafCount : Nat
endpointSemanticLeafCount = listLength endpointSemanticLeaves

residualLeafCount : Nat
residualLeafCount =
  sourceAnalysisLeafCount
  + sourceLiteralAttachmentLeafCount
  + endpointSemanticLeafCount
  where
  _+_ : Nat → Nat → Nat
  zero + n = n
  suc m + n = suc (m + n)

representedFiniteConvergenceCompilerLevel : ProofLevel
representedFiniteConvergenceCompilerLevel =
  R509.round509RepresentedExpectationConvergenceCompilerLevel

concreteEndpointSemanticsCompilerLevel : ProofLevel
concreteEndpointSemanticsCompilerLevel =
  R511.round511ConcreteEndpointSemanticsCompilerLevel

concreteEndpointConstructionCompilerLevel : ProofLevel
concreteEndpointConstructionCompilerLevel =
  R512.round512ConcreteEndpointConstructionCompilerLevel

a3ContinuumEndpointSemanticLeafStillResidual : Bool
a3ContinuumEndpointSemanticLeafStillResidual = false

a3SchwingerBelongingEndpointSemanticLeafStillResidual : Bool
a3SchwingerBelongingEndpointSemanticLeafStillResidual = false

t3OpaqueEndpointSemanticsStillResidual : Bool
t3OpaqueEndpointSemanticsStillResidual = false

bOpaqueGapEndpointSemanticsStillResidual : Bool
bOpaqueGapEndpointSemanticsStillResidual = false

g2OpaqueNontrivialityEndpointSemanticsStillResidual : Bool
g2OpaqueNontrivialityEndpointSemanticsStillResidual = false

structuralT1T4EndpointSemanticsStillResidual : Bool
structuralT1T4EndpointSemanticsStillResidual = true

round513ConcreteEndpointResidualCompilerLevel : ProofLevel
round513ConcreteEndpointResidualCompilerLevel = machineChecked
