{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanChargedCMP116SummabilityAttachmentRound362Exact where

------------------------------------------------------------------------
-- ROUND362 / H_sum = PUBLISHED CMP116 SUMMABILITY + SAME-OBJECT ATTACHMENTS
--
-- R354's selected H_sum is
--
--   sum selectedCharged selectedWalks <= selectedEnvelope.
--
-- The source boundary already records CMP116 generalized-walk localization and
-- residual tree/localisation summability as source-owned.  Therefore the live
-- work is not a fresh summation theorem.  It is to instantiate that theorem on
-- exactly the charged family produced after R355--R361.
--
-- This owner keeps the source theorem and the three application identifications
-- separate, then transports the source inequality mechanically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

record CMP116ChargedSummabilitySource (Walk : Set) : Set₁ where
  field
    sourceWalks : List Walk
    sourceChargedMajorant : Walk → ℝ
    sourceEnvelope : ℝ

    sourceChargedSummability :
      Resum.sumℝ sourceChargedMajorant sourceWalks ≤ℝ sourceEnvelope

open CMP116ChargedSummabilitySource public

record CMP116ChargedSummabilityAttachment {Walk : Set}
    (source : CMP116ChargedSummabilitySource Walk) : Set₁ where
  field
    selectedWalks : List Walk
    selectedChargedMajorant : Walk → ℝ
    selectedEnvelope : ℝ

    selectedWalksAreSourceWalks :
      selectedWalks ≡ sourceWalks source

    selectedChargedMajorantIsSourceMajorant :
      selectedChargedMajorant ≡ sourceChargedMajorant source

    selectedEnvelopeIsSourceEnvelope :
      selectedEnvelope ≡ sourceEnvelope source

open CMP116ChargedSummabilityAttachment public

selectedChargedSummability :
  ∀ {Walk}
    (source : CMP116ChargedSummabilitySource Walk)
    (attachment : CMP116ChargedSummabilityAttachment source) →
  Resum.sumℝ
    (selectedChargedMajorant attachment)
    (selectedWalks attachment)
    ≤ℝ
  selectedEnvelope attachment
selectedChargedSummability source attachment =
  subst
    (λ envelope →
      Resum.sumℝ
        (selectedChargedMajorant attachment)
        (selectedWalks attachment)
      ≤ℝ envelope)
    (sym (selectedEnvelopeIsSourceEnvelope attachment))
    (subst
      (λ majorant →
        Resum.sumℝ majorant (selectedWalks attachment)
          ≤ℝ sourceEnvelope source)
      (sym (selectedChargedMajorantIsSourceMajorant attachment))
      (subst
        (λ walks →
          Resum.sumℝ (sourceChargedMajorant source) walks
            ≤ℝ sourceEnvelope source)
        (sym (selectedWalksAreSourceWalks attachment))
        (sourceChargedSummability source)))

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

cmp116ResidualTreeSummabilitySourceLevel : ProofLevel
cmp116ResidualTreeSummabilitySourceLevel = standardImported

selectedChargedWalkFamilyAttachmentLevel : ProofLevel
selectedChargedWalkFamilyAttachmentLevel = conditional

selectedChargedMajorantAttachmentLevel : ProofLevel
selectedChargedMajorantAttachmentLevel = conditional

selectedChargedEnvelopeAttachmentLevel : ProofLevel
selectedChargedEnvelopeAttachmentLevel = conditional

summabilityTransportCompilerLevel : ProofLevel
summabilityTransportCompilerLevel = machineChecked

freshCMP116SummabilityTheoremRequired : Bool
freshCMP116SummabilityTheoremRequired = false

freshCMP116SummabilityTheoremRequiredIsFalse :
  freshCMP116SummabilityTheoremRequired ≡ false
freshCMP116SummabilityTheoremRequiredIsFalse = refl

sourceSummabilityAutomaticallyAppliesToSelectedFamily : Bool
sourceSummabilityAutomaticallyAppliesToSelectedFamily = false

sourceSummabilityAutomaticallyAppliesToSelectedFamilyIsFalse :
  sourceSummabilityAutomaticallyAppliesToSelectedFamily ≡ false
sourceSummabilityAutomaticallyAppliesToSelectedFamilyIsFalse = refl

record Round362Boundary : Set where
  constructor round362-boundary
  field
    sourceSummabilityOwned : Bool
    sourceSummabilityOwnedIsTrue : sourceSummabilityOwned ≡ true

    selectedFamilyAttachmentStillOpen : Bool
    selectedFamilyAttachmentStillOpenIsTrue :
      selectedFamilyAttachmentStillOpen ≡ true

    selectedMajorantAttachmentStillOpen : Bool
    selectedMajorantAttachmentStillOpenIsTrue :
      selectedMajorantAttachmentStillOpen ≡ true

    selectedEnvelopeAttachmentStillOpen : Bool
    selectedEnvelopeAttachmentStillOpenIsTrue :
      selectedEnvelopeAttachmentStillOpen ≡ true

canonicalRound362Boundary : Round362Boundary
canonicalRound362Boundary =
  round362-boundary true refl true refl true refl true refl

round362FrontierRefinementLevel : ProofLevel
round362FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
