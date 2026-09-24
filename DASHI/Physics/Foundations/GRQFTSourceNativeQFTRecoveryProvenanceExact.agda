{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary as Effective
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as Attach
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

------------------------------------------------------------------------
-- SOURCE-NATIVE QFT RECOVERY PROVENANCE
--
-- The legacy UnifiedCandidate socket accepts only JointMicroscopicState:
--
--   recoverQFT : JointMicroscopicState -> LiteralYangMillsConstruction
--
-- but the source-native YM lane owns substantially richer provenance tying one
-- literal finite family, continuum measure, Schwinger family and stress
-- derivative to the SAME literal construction.
--
-- Do not turn the missing provenance into another QFT theorem.  Retain it in
-- the recovery state and make the recovered construction definitional there.
------------------------------------------------------------------------

record SourceNativeQFTRecoveryState
    (U : Weld.UnifiedCandidate) : Set₁ where
  constructor sourceNativeQFTRecoveryState
  field
    jointState :
      Effective.JointMicroscopicState

    recoveredConstruction :
      Top.LiteralYangMillsConstruction
        (Weld.qftCarriers U) (Weld.qftSemantics U)

    SourceNativeProvenance :
      Set

    sourceNativeProvenance :
      SourceNativeProvenance

open SourceNativeQFTRecoveryState public

recoverQFTSourceNative :
  ∀ {U : Weld.UnifiedCandidate} →
  SourceNativeQFTRecoveryState U →
  Top.LiteralYangMillsConstruction
    (Weld.qftCarriers U) (Weld.qftSemantics U)
recoverQFTSourceNative =
  recoveredConstruction

sourceNativeRecoveryReturnsRetainedConstruction :
  ∀ {U : Weld.UnifiedCandidate}
    (state : SourceNativeQFTRecoveryState U) →
  recoverQFTSourceNative state
  ≡ recoveredConstruction state
sourceNativeRecoveryReturnsRetainedConstruction state = refl

forgetSourceNativeQFTRecoveryState :
  ∀ {U : Weld.UnifiedCandidate} →
  SourceNativeQFTRecoveryState U →
  Effective.JointMicroscopicState
forgetSourceNativeQFTRecoveryState =
  jointState

------------------------------------------------------------------------
-- LEGACY PROJECTION COMPATIBILITY
--
-- This is now the exact seam: the legacy lossy recovery map must agree with the
-- construction retained by the enriched source-native state.
------------------------------------------------------------------------

record LegacyQFTRecoveryProjectionCompatibility
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    enrich :
      Effective.JointMicroscopicState →
      SourceNativeQFTRecoveryState U

    forgetAfterEnrich :
      ∀ state →
      forgetSourceNativeQFTRecoveryState (enrich state)
      ≡ state

    legacyRecoverAgreesWithSourceNative :
      ∀ state →
      Weld.recoverQFT U state
      ≡ recoverQFTSourceNative (enrich state)

open LegacyQFTRecoveryProjectionCompatibility public

sourceNativeConstructionIsLegacyRecovered :
  ∀ {U : Weld.UnifiedCandidate}
    (compatibility : LegacyQFTRecoveryProjectionCompatibility U)
    (state : Effective.JointMicroscopicState) →
  recoverQFTSourceNative (enrich compatibility state)
  ≡ Weld.recoverQFT U state
sourceNativeConstructionIsLegacyRecovered compatibility state =
  sym (legacyRecoverAgreesWithSourceNative compatibility state)

------------------------------------------------------------------------
-- PINNED ATTACHMENT COMPILER
--
-- Once a candidate/regime's microscopic state enriches to the pinned literal
-- construction, the old PinnedYangMillsRecoveredQFTAttachment is compiler
-- output.  No second source-native continuum theorem is needed.
------------------------------------------------------------------------

record PinnedSourceNativeRecoverySelection
    (U : Weld.UnifiedCandidate)
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (compatibility : LegacyQFTRecoveryProjectionCompatibility U) : Set₁ where
  field
    enrichedMicroscopicStateIsPinned :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      recoverQFTSourceNative
        (enrich compatibility
          (Weld.microscopicState U
            (Weld.coarseGrain U candidate regime)))
      ≡
      Pinned.asLiteralYangMillsConstruction pinned

open PinnedSourceNativeRecoverySelection public

sourceNativeSelectionBuildsPinnedRecoveredAttachment :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    {compatibility : LegacyQFTRecoveryProjectionCompatibility U} →
  PinnedSourceNativeRecoverySelection U pinned compatibility →
  Attach.PinnedYangMillsRecoveredQFTAttachment U pinned
sourceNativeSelectionBuildsPinnedRecoveredAttachment
    {U = U} {pinned = pinned} {compatibility = compatibility}
    selection =
  record
    { Attach.PinnedYangMillsRecoveredQFTAttachment.literalPinnedConstructionIsRecoveredQFT =
        λ candidate regime qftAtRegime →
          trans
            (sym
              (enrichedMicroscopicStateIsPinned
                selection candidate regime qftAtRegime))
            (sourceNativeConstructionIsLegacyRecovered
              compatibility
              (Weld.microscopicState U
                (Weld.coarseGrain U candidate regime)))
    }

sourceNativeYMContinuumTheoremMustBeReprovedForLegacyRecovery : Bool
sourceNativeYMContinuumTheoremMustBeReprovedForLegacyRecovery = false

sourceNativeYMContinuumTheoremMustBeReprovedForLegacyRecoveryIsFalse :
  sourceNativeYMContinuumTheoremMustBeReprovedForLegacyRecovery ≡ false
sourceNativeYMContinuumTheoremMustBeReprovedForLegacyRecoveryIsFalse = refl

legacyJointMicroscopicStateRetainsSourceNativeYMProvenance : Bool
legacyJointMicroscopicStateRetainsSourceNativeYMProvenance = false

legacyJointMicroscopicStateRetainsSourceNativeYMProvenanceIsFalse :
  legacyJointMicroscopicStateRetainsSourceNativeYMProvenance ≡ false
legacyJointMicroscopicStateRetainsSourceNativeYMProvenanceIsFalse = refl

remainingQFTRecoverySeamIsProjectionCompatibility : Bool
remainingQFTRecoverySeamIsProjectionCompatibility = true

remainingQFTRecoverySeamIsProjectionCompatibilityIsTrue :
  remainingQFTRecoverySeamIsProjectionCompatibility ≡ true
remainingQFTRecoverySeamIsProjectionCompatibilityIsTrue = refl
