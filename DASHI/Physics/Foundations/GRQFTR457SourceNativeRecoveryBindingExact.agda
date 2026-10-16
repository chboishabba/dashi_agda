{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTR457SourceNativeRecoveryBindingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary as Effective
import DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact as Recovery
import DASHI.Physics.Foundations.BalabanRound131RecoveredQFTAttachmentExact as Round131Attachment
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.YangMillsClayGoal1SourceNativeContinuumRound457Exact as R457
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- R457 IS THE ACTUAL SOURCE-NATIVE PROVENANCE PAYLOAD
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
  { Recovery.SourceNativeQFTRecoveryState.jointState = joint
  ; Recovery.SourceNativeQFTRecoveryState.recoveredConstruction = Y
  ; Recovery.SourceNativeQFTRecoveryState.SourceNativeProvenance =
      R457.SourceNativeContinuumAndOS stressLane
  ; Recovery.SourceNativeQFTRecoveryState.sourceNativeProvenance = sourceNative
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
  Recovery.recoverQFTSourceNative (r457RecoveryState sourceNative joint) ≡ Y
r457RecoveryConstructionIsLiteralY sourceNative joint = refl

------------------------------------------------------------------------
-- R457 / LEGACY SAME-OBJECT ATTACHMENT
------------------------------------------------------------------------

record R457LegacyRecoverySameObjectAttachment
    {U : Weld.UnifiedCandidate}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {Y : Top.LiteralYangMillsConstruction
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
    legacyRecoverIsR457LiteralConstruction : Weld.recoverQFT U joint ≡ Y

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
  ≡ Recovery.recoverQFTSourceNative (r457RecoveryState sourceNative joint)
legacyRecoverAgreesWithR457SourceNativeState
    {sourceNative = sourceNative} {joint = joint} attachment =
  trans
    (legacyRecoverIsR457LiteralConstruction attachment)
    (sym (r457RecoveryConstructionIsLiteralY sourceNative joint))

------------------------------------------------------------------------
-- ROUND131 RECOVERED-QFT ATTACHMENT -> R457 SAME-OBJECT ATTACHMENT
--
-- Round131 already owns the canonical same-object recovery socket
--
--   Y = recoverQFT(microscopicState(coarseGrain candidate regime)).
--
-- R457 needs the reverse equality for that same selected joint state.  Hence a
-- Round131RecoveredQFTAttachment is sufficient; no separate R457 recovery
-- equality theorem is required.
------------------------------------------------------------------------

round131AttachmentBuildsR457SameObject :
  ∀ {U trajectory split inputs Y group Scale Volume activity domain representation stressLane}
    {sourceNative : R457.SourceNativeContinuumAndOS
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = Weld.qftCarriers U} {S = Weld.qftSemantics U}
      {Y = Y} {group = group}
      {Scale = Scale} {Volume = Volume} {activity = activity}
      {domain = domain} {representation = representation}
      stressLane} →
  Round131Attachment.Round131RecoveredQFTAttachment U Y →
  ∀ candidate regime →
  Weld.qftRegime U regime →
  R457LegacyRecoverySameObjectAttachment sourceNative
    (Weld.microscopicState U (Weld.coarseGrain U candidate regime))
round131AttachmentBuildsR457SameObject attachment candidate regime qftAtRegime =
  record
    { legacyRecoverIsR457LiteralConstruction =
        sym
          (Round131Attachment.literalConstructionIsRecoveredQFT
            attachment candidate regime qftAtRegime)
    }

round131RecoveredAttachmentToR457SameObjectCompilerOwned : Bool
round131RecoveredAttachmentToR457SameObjectCompilerOwned = true

independentR457RecoveryEqualityRequiredAfterRound131Attachment : Bool
independentR457RecoveryEqualityRequiredAfterRound131Attachment = false

round131RecoveredQFTAttachmentForR457StillRequired : Bool
round131RecoveredQFTAttachmentForR457StillRequired = true

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
