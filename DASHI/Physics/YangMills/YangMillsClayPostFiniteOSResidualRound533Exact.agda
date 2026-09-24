{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPostFiniteOSResidualRound533Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND533: RESIDUAL AFTER T1 -> FINITE-OS SAME-FAMILY REUSE
--
-- R528 counted Euclidean and Wilson-RP same-family applicability separately
-- from the concrete T1 source bundle.  R532 proves that on the preferred route
-- R462 takes both directly from that SAME T1 bundle.
--
-- Therefore those are not independent residual payments.
--
-- Preferred residual:
--
--   13 genuine non-C source-analysis leaves
--    5 remaining source<->literal attachments
--    2 rich structural/T1 source bundles
--    1 density->finite-measure map
--    5 C physical source packages
--   -----------------------------------
--   26 theorem/source obligations
--
-- Bosonic same-family applicability remains live.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
import DASHI.Physics.YangMills.YangMillsClayPostStructuralT1ResidualRound518Exact as R518
import DASHI.Physics.YangMills.YangMillsSourceFirstFiniteMeasureFromDensityRound525Exact as R525
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as R527
import DASHI.Physics.YangMills.YangMillsFiniteOSFromConcreteT1Round532Exact as R532

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
  ∷ R496.bWilsonTwoMarkExpansion
  ∷ R496.bWilsonConnectingWeightTail
  ∷ R496.bSameHamiltonianTransferCoordinate
  ∷ R496.g1ArbitraryCompactSimpleSourceMap
  ∷ []

sourceLiteralAttachmentLeaves : List R496.ResidualLeaf
sourceLiteralAttachmentLeaves =
    -- Euclidean and Wilson-RP are owned by the concrete T1 bundle via R532.
    R496.aFiniteBosonicSameObjectAttachment
  ∷ R496.a2BetaMarkGeneratedHistoryShell
  ∷ R496.a3CylinderEventIndicatorSemantics
  ∷ R496.a3CylinderExpectationIntegralIdentification
  ∷ R496.a45QuantitativeFiniteExpectationAttachment
  ∷ []

addedSourceLeaves : List R518.AddedSourceLeaf
addedSourceLeaves = R518.addedSourceLeaves

data DensityMeasureLeaf : Set where
  literalDensityToFiniteMeasureMap : DensityMeasureLeaf

densityMeasureLeafLevel : DensityMeasureLeaf → ProofLevel
densityMeasureLeafLevel literalDensityToFiniteMeasureMap =
  R525.literalRound525DensityToFiniteMeasureMapLevel

data CPackage : Set where
  c0WilsonLocalObservableRealization : CPackage
  c1MarkedCurvatureFamily : CPackage
  c2PhysicalRemainderTail : CPackage
  c3OneStepAFRecurrence : CPackage
  c4DensityAnchoredStressLane : CPackage

cPackageLevel : CPackage → ProofLevel
cPackageLevel c0WilsonLocalObservableRealization =
  R527.c0LiteralGaugeInvariantLocalObservableFamilyLevel
cPackageLevel c1MarkedCurvatureFamily =
  R527.c1MarkedCurvatureFamilyLevel
cPackageLevel c2PhysicalRemainderTail =
  R527.c2PhysicalRemainderSharedTailLevel
cPackageLevel c3OneStepAFRecurrence =
  R527.c3OneStepAFRecurrenceIdentificationLevel
cPackageLevel c4DensityAnchoredStressLane =
  R527.c4DensityAnchoredStressLaneLevel

densityMeasureLeaves : List DensityMeasureLeaf
densityMeasureLeaves = literalDensityToFiniteMeasureMap ∷ []

cPackages : List CPackage
cPackages =
    c0WilsonLocalObservableRealization
  ∷ c1MarkedCurvatureFamily
  ∷ c2PhysicalRemainderTail
  ∷ c3OneStepAFRecurrence
  ∷ c4DensityAnchoredStressLane
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)

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

independentFiniteEuclideanAttachmentRemaining : Bool
independentFiniteEuclideanAttachmentRemaining =
  R532.round532IndependentEuclideanApplicationRequired

independentFiniteWilsonRPAttachmentRemaining : Bool
independentFiniteWilsonRPAttachmentRemaining =
  R532.round532IndependentWilsonRPApplicationRequired

bosonicSameFamilyAttachmentRemaining : Bool
bosonicSameFamilyAttachmentRemaining = true

opaqueEndpointSemanticLeavesRemaining : Bool
opaqueEndpointSemanticLeavesRemaining = false

round533PostFiniteOSResidualCompilerLevel : ProofLevel
round533PostFiniteOSResidualCompilerLevel = machineChecked
