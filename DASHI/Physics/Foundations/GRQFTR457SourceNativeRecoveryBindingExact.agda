{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTR457SourceNativeRecoveryBindingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary as Effective
import DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact as Recovery
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.YangMillsClayGoal1SourceNativeContinuumRound457Exact as R457
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- R457 IS THE ACTUAL SOURCE-NATIVE PROVENANCE PAYLOAD
--
-- The generic enriched recovery state was deliberately representation-neutral.
-- This module instantiates its provenance coordinate with the repository's
-- actual R457 same-family continuum/OS certificate.
------------------------------------------------------------------------

r457RecoveryState :
  ∀ {U : Weld.UnifiedCandidate}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {Y :
      Top.LiteralYangMillsConstruction
        (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      domain representation} →
  R457.SourceNativeContinuumAndOS stressLane →
  Effective.JointMicroscopicState →
  Recovery.SourceNativeQFTRecoveryState U
r457RecoveryState {Y = Y} {stressLane = stressLane} sourceNative joint = record
  { Recovery.SourceNativeQFTRecoveryState.jointState =
      joint
  ; Recovery.SourceNativeQFTRecoveryState.recoveredConstruction =
      Y
  ; Recovery.SourceNativeQFTRecoveryState.SourceNativeProvenance =
      R457.SourceNativeContinuumAndOS stressLane
  ; Recovery.SourceNativeQFTRecoveryState.sourceNativeProvenance =
      sourceNative
  }

r457RecoveryConstructionIsLiteralY :
  ∀ {U : Weld.UnifiedCandidate}
    {trajectory split inputs Y group Scale Volume activity domain representation stressLane}
    (sourceNative : R457.SourceNativeContinuumAndOS
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane)
    joint →
  Recovery.recoverQFTSourceNative
    (r457RecoveryState sourceNative joint)
  ≡ Y
r457RecoveryConstructionIsLiteralY sourceNative joint = refl

------------------------------------------------------------------------
-- R457 / LEGACY SAME-OBJECT ATTACHMENT
--
-- Formal projection compatibility is now compiler-owned in
-- GRQFTSourceNativeQFTRecoveryProvenanceExact.  What remains physically is the
-- equality saying the legacy selected recovery actually returns the SAME
-- literal construction Y carried by this R457 continuum/OS certificate.
------------------------------------------------------------------------

record R457LegacyRecoverySameObjectAttachment
    {U : Weld.UnifiedCandidate}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {Y :
      Top.LiteralYangMillsConstruction
        (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      domain representation}
    (sourceNative : R457.SourceNativeContinuumAndOS stressLane)
    (joint : Effective.JointMicroscopicState) : Set₁ where
  field
    legacyRecoverIsR457LiteralConstruction :
      Weld.recoverQFT U joint ≡ Y

open R457LegacyRecoverySameObjectAttachment public

legacyRecoverAgreesWithR457SourceNativeState :
  ∀ {U trajectory split inputs Y group Scale Volume activity domain representation stressLane}
    {sourceNative : R457.SourceNativeContinuumAndOS
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane}
    {joint : Effective.JointMicroscopicState} →
  R457LegacyRecoverySameObjectAttachment sourceNative joint →
  Weld.recoverQFT U joint
  ≡ Recovery.recoverQFTSourceNative
      (r457RecoveryState sourceNative joint)
legacyRecoverAgreesWithR457SourceNativeState
    {sourceNative = sourceNative} {joint = joint} attachment =
  trans
    (legacyRecoverIsR457LiteralConstruction attachment)
    (sym (r457RecoveryConstructionIsLiteralY sourceNative joint))

r457ContinuumAndOSProvenanceRetainedInRecoveryState : Bool
r457ContinuumAndOSProvenanceRetainedInRecoveryState = true

r457ContinuumAndOSProvenanceRetainedInRecoveryStateIsTrue :
  r457ContinuumAndOSProvenanceRetainedInRecoveryState ≡ true
r457ContinuumAndOSProvenanceRetainedInRecoveryStateIsTrue = refl

additionalContinuumConstructionNeededForGRQFTRecoverQFT : Bool
additionalContinuumConstructionNeededForGRQFTRecoverQFT = false

additionalContinuumConstructionNeededForGRQFTRecoverQFTIsFalse :
  additionalContinuumConstructionNeededForGRQFTRecoverQFT ≡ false
additionalContinuumConstructionNeededForGRQFTRecoverQFTIsFalse = refl

legacyProjectionCompatibilityStillRequired : Bool
legacyProjectionCompatibilityStillRequired = false

legacyProjectionCompatibilityStillRequiredIsFalse :
  legacyProjectionCompatibilityStillRequired ≡ false
legacyProjectionCompatibilityStillRequiredIsFalse = refl

r457LegacyRecoverySameObjectAttachmentStillRequired : Bool
r457LegacyRecoverySameObjectAttachmentStillRequired = true

r457LegacyRecoverySameObjectAttachmentStillRequiredIsTrue :
  r457LegacyRecoverySameObjectAttachmentStillRequired ≡ true
r457LegacyRecoverySameObjectAttachmentStillRequiredIsTrue = refl
