module DASHI.Physics.ExoticGravity.AntigravityJointProofSearchFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Coupling
import DASHI.Physics.ExoticGravity.LiTorrStandardGRComparatorBidiExact as GRComparator
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Enhancement
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan

------------------------------------------------------------------------
-- JOINT FRONTIER VIEW
--
-- This is not a new planner.  It packages the exact states already owned by
-- five existing BIDI routers so proof search can see their shared live cut.
------------------------------------------------------------------------

record JointFrontier : Set where
  constructor joint-frontier
  field
    evidenceState : Evidence.EvidenceClosureState
    couplingState : Coupling.AlphaClosureState
    grComparatorState : GRComparator.GRComparatorState
    geometryState : Geometry.GeometryClosureState
    enhancementState : Enhancement.EnhancementClosureState

open JointFrontier public

currentJointFrontier : JointFrontier
currentJointFrontier = joint-frontier
  Evidence.currentPublicConstraintState
  Coupling.currentAlphaFrontier
  GRComparator.currentGRComparatorFrontier
  Geometry.currentHistoricalGeometryState
  Enhancement.currentEnhancementFrontier

------------------------------------------------------------------------
-- Exact current first-open vector.
------------------------------------------------------------------------

currentEvidenceFirstOpen :
  Evidence.firstOpenEvidenceLeaf (evidenceState currentJointFrontier)
    ≡ Evidence.sourceCharacterisationLeaf
currentEvidenceFirstOpen = refl

currentCouplingFirstOpen :
  Coupling.firstOpenAlphaLeaf (couplingState currentJointFrontier)
    ≡ Coupling.sourceObservableLeaf
currentCouplingFirstOpen = refl

currentGRComparatorFirstOpen :
  GRComparator.firstOpenGRComparatorLeaf (grComparatorState currentJointFrontier)
    ≡ GRComparator.apparatusGeometryLeaf
currentGRComparatorFirstOpen = refl

currentGeometryFirstOpen :
  Geometry.firstOpenGeometryLeaf (geometryState currentJointFrontier)
    ≡ Geometry.sourceShapeLeaf
currentGeometryFirstOpen = refl

currentEnhancementFirstOpen :
  Enhancement.firstOpenEnhancementLeaf (enhancementState currentJointFrontier)
    ≡ Enhancement.sourceCurrentLeaf
currentEnhancementFirstOpen = refl

------------------------------------------------------------------------
-- Bundle stages are the already-defined optimized payment targets.
------------------------------------------------------------------------

data JointBundleStage : Set where
  sourceGeometryBundle : JointBundleStage
  phaseProbeBundle : JointBundleStage
  ordinaryModelBundle : JointBundleStage
  scalingReplicationBundle : JointBundleStage
  comparisonFrontier : JointBundleStage

currentRecommendedBundle : JointBundleStage
currentRecommendedBundle = sourceGeometryBundle

currentRecommendationIsSourceGeometry :
  currentRecommendedBundle ≡ sourceGeometryBundle
currentRecommendationIsSourceGeometry = refl

------------------------------------------------------------------------
-- Hypothetical post-payment joint frontiers.  These reuse Plan's states exactly;
-- they are not claims that the empirical receipts already exist.
------------------------------------------------------------------------

postSourceJointFrontier : JointFrontier
postSourceJointFrontier = joint-frontier
  Plan.postSourceEvidenceState
  Plan.postSourceCouplingState
  Plan.postSourceComparatorState
  Plan.postSourceGeometryState
  Plan.postSourceEnhancementState

postPhaseJointFrontier : JointFrontier
postPhaseJointFrontier = joint-frontier
  Plan.postPhaseEvidenceState
  Plan.postPhaseCouplingState
  Plan.postSourceComparatorState
  Plan.postSourceGeometryState
  Plan.postPhaseEnhancementState

postOrdinaryJointFrontier : JointFrontier
postOrdinaryJointFrontier = joint-frontier
  Plan.postOrdinaryEvidenceState
  Plan.postOrdinaryCouplingState
  Plan.postOrdinaryComparatorState
  Plan.postSourceGeometryState
  Plan.postOrdinaryEnhancementState

postScalingJointFrontier : JointFrontier
postScalingJointFrontier = joint-frontier
  Plan.postScalingEvidenceState
  Plan.postScalingCouplingState
  Plan.postOrdinaryComparatorState
  Plan.postSourceGeometryState
  Plan.postScalingEnhancementState

------------------------------------------------------------------------
-- Exact stage recomputation.
------------------------------------------------------------------------

postSourceNextEvidence :
  Evidence.firstOpenEvidenceLeaf (evidenceState postSourceJointFrontier)
    ≡ Evidence.transitionLockLeaf
postSourceNextEvidence = refl

postSourceNextCoupling :
  Coupling.firstOpenAlphaLeaf (couplingState postSourceJointFrontier)
    ≡ Coupling.externalProbeLeaf
postSourceNextCoupling = refl

postSourceGRNeedsSolver :
  GRComparator.firstOpenGRComparatorLeaf (grComparatorState postSourceJointFrontier)
    ≡ GRComparator.weakFieldSolverLeaf
postSourceGRNeedsSolver = refl

postSourceGeometryClosed :
  Geometry.firstOpenGeometryLeaf (geometryState postSourceJointFrontier)
    ≡ Geometry.closedGeometry
postSourceGeometryClosed = refl

postSourceEnhancementNeedsPhaseMatchedField :
  Enhancement.firstOpenEnhancementLeaf (enhancementState postSourceJointFrontier)
    ≡ Enhancement.phaseMatchedFieldLeaf
postSourceEnhancementNeedsPhaseMatchedField = refl

postPhaseNextEvidence :
  Evidence.firstOpenEvidenceLeaf (evidenceState postPhaseJointFrontier)
    ≡ Evidence.backgroundClosureLeaf
postPhaseNextEvidence = refl

postPhaseNextCoupling :
  Coupling.firstOpenAlphaLeaf (couplingState postPhaseJointFrontier)
    ≡ Coupling.ordinaryGRLeaf
postPhaseNextCoupling = refl

postPhaseEnhancementNeedsBackgrounds :
  Enhancement.firstOpenEnhancementLeaf (enhancementState postPhaseJointFrontier)
    ≡ Enhancement.backgroundClosureLeaf
postPhaseEnhancementNeedsBackgrounds = refl

postOrdinaryNextEvidence :
  Evidence.firstOpenEvidenceLeaf (evidenceState postOrdinaryJointFrontier)
    ≡ Evidence.constitutiveResidualLeaf
postOrdinaryNextEvidence = refl

postOrdinaryNextCoupling :
  Coupling.firstOpenAlphaLeaf (couplingState postOrdinaryJointFrontier)
    ≡ Coupling.reproducibilityLeaf
postOrdinaryNextCoupling = refl

postOrdinaryGRClosed :
  GRComparator.firstOpenGRComparatorLeaf (grComparatorState postOrdinaryJointFrontier)
    ≡ GRComparator.comparatorClosed
postOrdinaryGRClosed = refl

postOrdinaryEnhancementNeedsRatio :
  Enhancement.firstOpenEnhancementLeaf (enhancementState postOrdinaryJointFrontier)
    ≡ Enhancement.constitutiveRatioLeaf
postOrdinaryEnhancementNeedsRatio = refl

postScalingEvidenceBounded :
  Evidence.firstOpenEvidenceLeaf (evidenceState postScalingJointFrontier)
    ≡ Evidence.boundedNoPromotionLeaf
postScalingEvidenceBounded = refl

postScalingCouplingClosed :
  Coupling.firstOpenAlphaLeaf (couplingState postScalingJointFrontier)
    ≡ Coupling.alphaClosed
postScalingCouplingClosed = refl

postScalingGRClosed :
  GRComparator.firstOpenGRComparatorLeaf (grComparatorState postScalingJointFrontier)
    ≡ GRComparator.comparatorClosed
postScalingGRClosed = refl

postScalingGeometryClosed :
  Geometry.firstOpenGeometryLeaf (geometryState postScalingJointFrontier)
    ≡ Geometry.closedGeometry
postScalingGeometryClosed = refl

postScalingEnhancementClosed :
  Enhancement.firstOpenEnhancementLeaf (enhancementState postScalingJointFrontier)
    ≡ Enhancement.closedEnhancementSplit
postScalingEnhancementClosed = refl

------------------------------------------------------------------------
-- Boundary: joint visibility changes scheduling only; it does not merge owners
-- or turn hypothetical post-payment states into current empirical facts.
------------------------------------------------------------------------

record JointFrontierBoundary : Set where
  constructor joint-frontier-boundary
  field
    jointViewReplacesUnderlyingStateMachines : Bool
    currentSharedFrontierIsSourceFacing : Bool
    sourceBundleMayAdvanceAllFiveConsumers : Bool
    sourceBundleCandidateAutomaticallyPaysAllFive : Bool
    hypotheticalPostPaymentStateEqualsCurrentEvidence : Bool
    postScalingJointClosureAutomaticallyProvesAntigravity : Bool
    postScalingJointClosureMayAdvanceToTheoryComparison : Bool

canonicalJointFrontierBoundary : JointFrontierBoundary
canonicalJointFrontierBoundary =
  joint-frontier-boundary
    false true true false false false true
