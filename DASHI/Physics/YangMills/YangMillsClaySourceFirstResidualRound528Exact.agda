{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClaySourceFirstResidualRound528Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND528: SOURCE-FIRST CONCRETE-SEMANTICS RESIDUAL
--
-- Starting from R521's 33 honest residuals:
--
--   R524/R526:
--     source OS system is constructed directly on the represented Schwinger
--     function; the historical R127 source-OS/literal-Schwinger weld is gone.
--
--   R525:
--     literal finite family at fixed G is chosen as the image of the literal
--     beta-driven density.  Replace the density/family equality by the genuine
--     density -> normalized finite-measure source map.
--
--   R527:
--     nine flattened C leaves are four physical source packages.
--
-- Result:
--
--   13 genuine analytic/source leaves
--    7 source<->literal applicability attachments
--    2 rich structural/T1 source bundles
--    1 density->finite-measure source map
--    4 C physical source packages
--   -----------------------------------
--   27 preferred residual theorem/source packages
--
-- No opaque endpoint semantic leaf remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
import DASHI.Physics.YangMills.YangMillsClayPostStructuralT1ResidualRound518Exact as R518
import DASHI.Physics.YangMills.YangMillsSourceFirstFiniteMeasureFromDensityRound525Exact as R525
import DASHI.Physics.YangMills.YangMillsRepresentedPublishedOSAssemblyRound526Exact as R526
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as R527

------------------------------------------------------------------------
-- Thirteen still-genuine non-C source mathematics leaves.
------------------------------------------------------------------------

sourceAnalysisLeaves : List R496.ResidualLeaf
sourceAnalysisLeaves =
    -- A1 current-step source calculation chain.
    R496.a1WilsonHessianVariation
  ∷ R496.a1AveragingConstraintVariation
  ∷ R496.a1GaugeProjectionVariation
  ∷ R496.a1WQRAssembly
  ∷ R496.a1ConstrainedGaussianMixedCoefficient
  ∷ R496.a1PhysicalJetFiveChannelSplit
  ∷ R496.a1FourJointReceiptEvaluation

    -- A3 representation theorem package.
  ∷ R496.a3ProjectiveEventExpectationConsistency
  ∷ R496.a3ContinuityAtEmpty

    -- B source-correct Wilson/spectral gap.
  ∷ R496.bWilsonTwoMarkExpansion
  ∷ R496.bWilsonConnectingWeightTail
  ∷ R496.bSameHamiltonianTransferCoordinate

    -- arbitrary compact-simple quantitative source map.
  ∷ R496.g1ArbitraryCompactSimpleSourceMap
  ∷ []

------------------------------------------------------------------------
-- Seven remaining applicability/same-source attachments.
------------------------------------------------------------------------

sourceLiteralAttachmentLeaves : List R496.ResidualLeaf
sourceLiteralAttachmentLeaves =
    R496.aFiniteEuclideanSameObjectAttachment
  ∷ R496.aFiniteBosonicSameObjectAttachment
  ∷ R496.aFiniteWilsonRPSameObjectAttachment
  ∷ R496.a2BetaMarkGeneratedHistoryShell
  ∷ R496.a3CylinderEventIndicatorSemantics
  ∷ R496.a3CylinderExpectationIntegralIdentification
  ∷ R496.a45QuantitativeFiniteExpectationAttachment
  ∷ []

------------------------------------------------------------------------
-- Rich source objects replacing opaque endpoint predicates.
------------------------------------------------------------------------

addedSourceLeaves : List R518.AddedSourceLeaf
addedSourceLeaves = R518.addedSourceLeaves

data DensityMeasureLeaf : Set where
  literalDensityToFiniteMeasureMap : DensityMeasureLeaf

densityMeasureLeafLevel : DensityMeasureLeaf → ProofLevel
densityMeasureLeafLevel literalDensityToFiniteMeasureMap =
  R525.literalRound525DensityToFiniteMeasureMapLevel

densityMeasureLeaves : List DensityMeasureLeaf
densityMeasureLeaves = literalDensityToFiniteMeasureMap ∷ []

data CPackage : Set where
  c1MarkedCurvatureFamily : CPackage
  c2PhysicalRemainderTail : CPackage
  c3OneStepAFRecurrence : CPackage
  c4DensityAnchoredStressLane : CPackage

cPackageLevel : CPackage → ProofLevel
cPackageLevel c1MarkedCurvatureFamily =
  R527.c1MarkedCurvatureFamilyLevel
cPackageLevel c2PhysicalRemainderTail =
  R527.c2PhysicalRemainderSharedTailLevel
cPackageLevel c3OneStepAFRecurrence =
  R527.c3OneStepAFRecurrenceIdentificationLevel
cPackageLevel c4DensityAnchoredStressLane =
  R527.c4DensityAnchoredStressLaneLevel

cPackages : List CPackage
cPackages =
    c1MarkedCurvatureFamily
  ∷ c2PhysicalRemainderTail
  ∷ c3OneStepAFRecurrence
  ∷ c4DensityAnchoredStressLane
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

sourceAnalysisLeafCount : Nat
sourceAnalysisLeafCount = listLength sourceAnalysisLeaves

sourceLiteralAttachmentLeafCount : Nat
sourceLiteralAttachmentLeafCount =
  listLength sourceLiteralAttachmentLeaves

addedSourceLeafCount : Nat
addedSourceLeafCount = listLength addedSourceLeaves

densityMeasureLeafCount : Nat
densityMeasureLeafCount = listLength densityMeasureLeaves

cPhysicalPackageCount : Nat
cPhysicalPackageCount = listLength cPackages

residualLeafCount : Nat
residualLeafCount =
  add sourceAnalysisLeafCount
    (add sourceLiteralAttachmentLeafCount
      (add addedSourceLeafCount
        (add densityMeasureLeafCount cPhysicalPackageCount)))
  where
  add : Nat → Nat → Nat
  add zero n = n
  add (suc m) n = suc (add m n)

opaqueEndpointSemanticLeavesRemaining : Bool
opaqueEndpointSemanticLeavesRemaining = false

sourceOSLiteralSchwingerWeldRemaining : Bool
sourceOSLiteralSchwingerWeldRemaining =
  R526.round526SourceOSLiteralSchwingerWeldRequired

densityLiteralFiniteFamilyEqualityRemaining : Bool
densityLiteralFiniteFamilyEqualityRemaining = false

representedOSExtensionalityAssumptionRemaining : Bool
representedOSExtensionalityAssumptionRemaining = false

round528SourceFirstResidualCompilerLevel : ProofLevel
round528SourceFirstResidualCompilerLevel = machineChecked
