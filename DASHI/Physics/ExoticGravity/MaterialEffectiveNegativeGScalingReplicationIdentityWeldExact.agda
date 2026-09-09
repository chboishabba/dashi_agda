module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as GR
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact as Ratio
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Coupling
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Enhancement

------------------------------------------------------------------------
-- SAME-OBJECT WELD: TYPED eta_C MEASUREMENT <-> EXISTING SCALING/REPLICATION
------------------------------------------------------------------------

record ScalingReplicationIdentityWeld
    {prediction : GR.OrdinaryGRPredictionReceipt}
    (ratio : Ratio.ConstitutiveRatioMeasurementReceipt prediction)
    (bundle : Plan.ScalingReplicationBundleReceipt) : Set where
  constructor scaling-replication-identity-weld
  field
    sameApparatus :
      Ratio.apparatusIdentity ratio ≡ Plan.apparatusCarrier bundle

    sameReplicationCarrier :
      Ratio.replicationCarrier ratio ≡ Plan.replicationCarrier bundle

    sameScalingSweepCarrier :
      Ratio.scalingSweepCarrier ratio ≡ Plan.scalingSweepCarrier bundle

    constitutiveRatioPaidInBundle :
      Enhancement.constitutiveRatioOwned
        (Plan.enhancementState bundle) ≡ true

    replicationPaidInCoupling :
      Coupling.replicated (Plan.couplingState bundle) ≡ true

    scalingLawPaidInCoupling :
      Coupling.scalingLawOwned (Plan.couplingState bundle) ≡ true

    constitutiveResidualPaidInEvidence :
      Evidence.constitutiveResidualOwned
        (Plan.evidenceState bundle) ≡ true

open ScalingReplicationIdentityWeld public

------------------------------------------------------------------------
-- Existing post-scaling endpoint retained exactly.
------------------------------------------------------------------------

postScalingEvidenceIsBounded :
  Evidence.firstOpenEvidenceLeaf Plan.postScalingEvidenceState
    ≡ Evidence.boundedNoPromotionLeaf
postScalingEvidenceIsBounded = Plan.postScalingEvidenceBounded

postScalingCouplingIsClosed :
  Coupling.firstOpenAlphaLeaf Plan.postScalingCouplingState
    ≡ Coupling.alphaClosed
postScalingCouplingIsClosed = Plan.postScalingCouplingClosed

postScalingEnhancementIsClosed :
  Enhancement.firstOpenEnhancementLeaf Plan.postScalingEnhancementState
    ≡ Enhancement.closedEnhancementSplit
postScalingEnhancementIsClosed = Plan.postScalingEnhancementClosed

record ScalingReplicationIdentityBoundary : Set where
  constructor scaling-replication-identity-boundary
  field
    sameLabelMaySubstituteForSameReplicationCarrier : Bool
    differentScalingSweepMayPaySameTypedRatio : Bool
    apparatusIdentityMayDriftBetweenRatioAndReplication : Bool
    exactReplicationCarrierEqualityRequired : Bool
    exactScalingSweepCarrierEqualityRequired : Bool
    exactApparatusEqualityRequired : Bool
    closedScalingStateAutomaticallyProvesNegativeEffectiveG : Bool
    closedScalingStateMayFeedTypedNegativeGComparison : Bool

canonicalScalingReplicationIdentityBoundary : ScalingReplicationIdentityBoundary
canonicalScalingReplicationIdentityBoundary =
  scaling-replication-identity-boundary
    false false false true true true false true
