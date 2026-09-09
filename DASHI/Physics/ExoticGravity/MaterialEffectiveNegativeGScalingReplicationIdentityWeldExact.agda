module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as GR
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact as Ratio
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Coupling
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Enhancement
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact as NegativeG
import DASHI.Physics.ExoticGravity.SuperconductingResidualCouplingNegativeGInterpretationBidiExact as Interpretation
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope

------------------------------------------------------------------------
-- SAME-OBJECT WELD: TYPED eta_C MEASUREMENT <-> EXISTING SCALING/REPLICATION
--
-- This is the only compiler boundary from the typed ratio measurement into
-- the existing material-effective negative-G interpretation.  A ratio receipt
-- alone is deliberately insufficient: it must be welded to the exact canonical
-- scaling/replication bundle that pays the existing evidence/coupling/
-- enhancement state machines.
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
-- Least-privilege compiler into the already-existing negative-G weld.
------------------------------------------------------------------------

compileConstitutiveNegativeGReceipt :
  {prediction : GR.OrdinaryGRPredictionReceipt} →
  {ratio : Ratio.ConstitutiveRatioMeasurementReceipt prediction} →
  {bundle : Plan.ScalingReplicationBundleReceipt} →
  ScalingReplicationIdentityWeld ratio bundle →
  NegativeG.ConstitutiveNegativeGReceipt
compileConstitutiveNegativeGReceipt {ratio = ratio} weld =
  NegativeG.constitutive-negative-g-receipt
    (Ratio.factorization ratio)
    Enhancement.constitutiveChange
    refl
    (Ratio.FixedMeasuredSourceComparison ratio)
    (Ratio.fixedMeasuredSourceComparison ratio)
    (Ratio.standardCoefficientSign ratio)
    (Ratio.standardCoefficientIsPositive ratio)
    (Ratio.candidateCoefficientSign ratio)
    (Ratio.candidateCoefficientIsNegative ratio)
    Interpretation.materialEffectiveGCouplingModification
    refl
    Scope.materialEffectiveCoupling
    refl
    (Ratio.ConstitutiveSignMapping ratio)
    (Ratio.constitutiveSignMapping ratio)

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
    typedRatioAloneMayCompileExistingNegativeGWeld : Bool
    identityWeldMayCompileExistingNegativeGWeld : Bool
    closedScalingStateAutomaticallyProvesNegativeEffectiveG : Bool
    compiledNegativeGWeldProvesUniversalNegativeG : Bool
    compiledNegativeGWeldProvesPhysicalCorrectness : Bool

canonicalScalingReplicationIdentityBoundary : ScalingReplicationIdentityBoundary
canonicalScalingReplicationIdentityBoundary =
  scaling-replication-identity-boundary
    false false false true true true false true false false false
