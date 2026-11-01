module DASHI.Physics.Closure.YMResidualTermMembershipResolver where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core

------------------------------------------------------------------------
-- Resolver layer for PolymerIn.
--
-- The original PolymerIn relation is intentionally weak: it is just an
-- identifier witness.  This module does not mutate that relation globally.
-- Instead, it defines the stronger resolver object needed by Sprint 82:
-- every membership witness must resolve to an actual residual term and the
-- polymer support links must be term-use links for that residual term.

actionTermFromResidualEffectiveActionTerm :
  Support.ResidualEffectiveActionTerm →
  Core.ActionTerm
actionTermFromResidualEffectiveActionTerm term =
  Core.actionTerm (Support.termId term) Core.residualSector

residualActionTermFromResidualFlag :
  (term : Support.ResidualEffectiveActionTerm) →
  Support.residualAfterTransferAbsorption term ≡ true →
  Core.ResidualActionTerm (actionTermFromResidualEffectiveActionTerm term)
residualActionTermFromResidualFlag term residualFlag =
  Core.residualActionTerm refl

record PolymerInResidualTermResolver : Set₁ where
  field
    residualTermForMembership :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      Support.PolymerIn S γ →
      Support.ResidualEffectiveActionTerm

    residualTermForMembershipIsResidual :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      (member : Support.PolymerIn S γ) →
      Support.residualAfterTransferAbsorption
        (residualTermForMembership S γ member)
        ≡ true

    membershipSupportLinksUseResidualTerm :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      (member : Support.PolymerIn S γ) →
      Core.AllTermUsesLinks
        (actionTermFromResidualEffectiveActionTerm
          (residualTermForMembership S γ member))
        (Support.supportLinks γ)

open PolymerInResidualTermResolver public

residualPolymerTermSupportSemanticsFromResolver :
  PolymerInResidualTermResolver →
  Core.ResidualPolymerTermSupportSemantics
residualPolymerTermSupportSemanticsFromResolver resolver =
  record
    { residualTermForPolymer = λ S γ member →
          actionTermFromResidualEffectiveActionTerm
            (residualTermForMembership resolver S γ member)
    ; residualTermForPolymerIsResidual = λ S γ member →
          residualActionTermFromResidualFlag
            (residualTermForMembership resolver S γ member)
            (residualTermForMembershipIsResidual resolver S γ member)
    ; polymerSupportLinksUseResidualTerm =
        membershipSupportLinksUseResidualTerm resolver
    }

record ResolverLayerDefined : Set₂ where
  field
    resolverCarrierDefined :
      PolymerInResidualTermResolver ≡ PolymerInResidualTermResolver
    actionTermFromResidualTermDefined :
      actionTermFromResidualEffectiveActionTerm
        ≡ actionTermFromResidualEffectiveActionTerm
    residualSemanticsAssemblyDefined :
      residualPolymerTermSupportSemanticsFromResolver
        ≡ residualPolymerTermSupportSemanticsFromResolver

resolverLayerDefined : ResolverLayerDefined
resolverLayerDefined =
  record
    { resolverCarrierDefined = refl
    ; actionTermFromResidualTermDefined = refl
    ; residualSemanticsAssemblyDefined = refl
    }

polymerInResidualTermResolverProvedForBalabanEffectiveAction : Bool
polymerInResidualTermResolverProvedForBalabanEffectiveAction = false

residualPolymerTermSupportSemanticsUnconditional : Bool
residualPolymerTermSupportSemanticsUnconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data ResolverLayerPromotion : Set where

resolverLayerPromotionImpossibleHere :
  ResolverLayerPromotion →
  ⊥
resolverLayerPromotionImpossibleHere ()

record ResolverLayerBoundary : Set₂ where
  field
    resolverLayerIsDefined :
      ResolverLayerDefined
    balabanResolverStillOpen :
      polymerInResidualTermResolverProvedForBalabanEffectiveAction ≡ false
    residualSupportSemanticsStillConditional :
      residualPolymerTermSupportSemanticsUnconditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      ResolverLayerPromotion → ⊥

resolverLayerBoundary : ResolverLayerBoundary
resolverLayerBoundary =
  record
    { resolverLayerIsDefined = resolverLayerDefined
    ; balabanResolverStillOpen = refl
    ; residualSupportSemanticsStillConditional = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = resolverLayerPromotionImpossibleHere
    }
