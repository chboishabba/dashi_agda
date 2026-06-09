module DASHI.Physics.Closure.YMGateBInRepoDerivationAttempts where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using (_∷_; [])

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMProviderSemanticObligations as Obligations
import DASHI.Physics.Closure.YMResolvedMembershipSemantics as Membership
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMTemporalTransferSemanticBridge as Transfer

------------------------------------------------------------------------
-- Sprint 83 in-repo derivation attempts.
--
-- This module pushes the two live Gate-B derivation blockers against the
-- current carriers.  It proves the part that is genuinely constructible and
-- records counterexamples for the parts that are not.

temporalOrMixedTermAbsorbedByCurrentConstructor :
  (t : Core.ActionTerm) →
  Core.TemporalOrMixedTerm t →
  Core.TransferMatrixTerm t
temporalOrMixedTermAbsorbedByCurrentConstructor t temporal =
  Core.transferMatrixTerm
    (Core.TemporalOrMixedTerm.temporalOrMixedIsTransfer temporal)

temporalAbsorptionSemanticsFromCurrentConstructors :
  Obligations.TemporalAbsorptionSemantics
temporalAbsorptionSemanticsFromCurrentConstructors =
  record
    { temporalOrMixedTermAbsorbedIntoTransferMatrix =
        temporalOrMixedTermAbsorbedByCurrentConstructor
    }

transferResidualExclusionSemanticsFromCurrentSectors :
  Obligations.TransferResidualExclusionSemantics
transferResidualExclusionSemanticsFromCurrentSectors =
  record
    { transferMatrixTermsExcludedFromResidual =
        Core.transferMatrixTermNotResidualBySector
    }

typedTemporalTransferInterpretationFromCurrentSectors :
  Transfer.TypedTemporalTransferInterpretation
typedTemporalTransferInterpretationFromCurrentSectors =
  record
    { temporalOrMixedTermAbsorbed =
        temporalOrMixedTermAbsorbedByCurrentConstructor
    ; transferTermExcludedFromResidual =
        Core.transferMatrixTermNotResidualBySector
    }

receiptBackedTemporalTransferInterpretationFromCurrentSectors :
  Transfer.ReceiptBackedTemporalTransferInterpretation
receiptBackedTemporalTransferInterpretationFromCurrentSectors =
  record
    { sprint71MixedPlaquetteBookkeepingClosed = refl
    ; sprint78ConditionalReceiptSurfaceRecorded = refl
    ; typedInterpretation =
        typedTemporalTransferInterpretationFromCurrentSectors
    }

residualTermMembershipInEmptyImpossible :
  (term : Support.ResidualEffectiveActionTerm) →
  Membership._∈ResidualTerms_ term []
  → ⊥
residualTermMembershipInEmptyImpossible term ()

weakPolymerInStrongResidualRefinementImpossibleForCurrentCarriers :
  Membership.PolymerInRefinesToStrongResidualMembership →
  ⊥
weakPolymerInStrongResidualRefinementImpossibleForCurrentCarriers refinement =
  residualTermMembershipInEmptyImpossible
    (Membership.StrongResidualPolymerMembership.resolvedResidualTerm strong)
    (Membership.StrongResidualPolymerMembership.resolvedTermInEffectiveAction
      strong)
  where
    temporalLink : Support.Link
    temporalLink =
      Support.link "weak-membership-temporal-link" Support.temporal

    temporalPolymer : Support.Polymer
    temporalPolymer =
      Support.polymer "weak-membership-polymer" (temporalLink ∷ [])

    emptyAction : Support.BalabanEffectiveAction
    emptyAction =
      Support.balabanEffectiveAction "weak-membership-empty-action" []

    weakMember : Support.PolymerIn emptyAction temporalPolymer
    weakMember =
      Support.polymerIn "weak-member-has-no-residual-term"

    strong :
      Membership.StrongResidualPolymerMembership emptyAction temporalPolymer
    strong =
      Membership.PolymerInRefinesToStrongResidualMembership.refinePolymerIn
        refinement
        emptyAction
        temporalPolymer
        weakMember

temporalAbsorptionSemanticsDerivedInRepo : Bool
temporalAbsorptionSemanticsDerivedInRepo = true

transferResidualExclusionSemanticsDerivedInRepo : Bool
transferResidualExclusionSemanticsDerivedInRepo = true

typedTemporalTransferInterpretationDerivedInRepo : Bool
typedTemporalTransferInterpretationDerivedInRepo = true

weakPolymerInStrongResidualRefinementRefutedForCurrentCarriers : Bool
weakPolymerInStrongResidualRefinementRefutedForCurrentCarriers = true

gateBPackagingResolutionEvidenceDerivedInRepo : Bool
gateBPackagingResolutionEvidenceDerivedInRepo = false

eta4EarnedUnconditional : Bool
eta4EarnedUnconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data GateBDerivationAttemptPromotion : Set where

gateBDerivationAttemptPromotionImpossibleHere :
  GateBDerivationAttemptPromotion →
  ⊥
gateBDerivationAttemptPromotionImpossibleHere ()

record GateBInRepoDerivationAttemptBoundary : Set where
  field
    temporalAbsorptionDerived :
      temporalAbsorptionSemanticsDerivedInRepo ≡ true
    transferResidualExclusionDerived :
      transferResidualExclusionSemanticsDerivedInRepo ≡ true
    typedTemporalTransferDerived :
      typedTemporalTransferInterpretationDerivedInRepo ≡ true
    weakToStrongMembershipRefuted :
      weakPolymerInStrongResidualRefinementRefutedForCurrentCarriers ≡ true
    packagingEvidenceNotDerived :
      gateBPackagingResolutionEvidenceDerivedInRepo ≡ false
    eta4NotUnconditional :
      eta4EarnedUnconditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      GateBDerivationAttemptPromotion → ⊥

gateBInRepoDerivationAttemptBoundary :
  GateBInRepoDerivationAttemptBoundary
gateBInRepoDerivationAttemptBoundary =
  record
    { temporalAbsorptionDerived = refl
    ; transferResidualExclusionDerived = refl
    ; typedTemporalTransferDerived = refl
    ; weakToStrongMembershipRefuted = refl
    ; packagingEvidenceNotDerived = refl
    ; eta4NotUnconditional = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere =
        gateBDerivationAttemptPromotionImpossibleHere
    }
