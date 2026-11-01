module DASHI.Physics.Closure.YMResolvedMembershipSemantics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMProviderSemanticObligations as Obligations
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver

------------------------------------------------------------------------
-- Strong residual-term membership semantics.
--
-- The weak PolymerIn relation is intentionally just an identifier.  This
-- module adds the missing refinement: a polymer membership is meaningful for
-- Gate B only when it resolves to an actual residual effective-action term in
-- the residualTerms list, with the right polymer and support-use semantics.

data _∈ResidualTerms_
  (term : Support.ResidualEffectiveActionTerm) :
  List Support.ResidualEffectiveActionTerm → Set where
  here :
    {terms : List Support.ResidualEffectiveActionTerm} →
    term ∈ResidualTerms (term ∷ terms)
  there :
    {other : Support.ResidualEffectiveActionTerm} →
    {terms : List Support.ResidualEffectiveActionTerm} →
    term ∈ResidualTerms terms →
    term ∈ResidualTerms (other ∷ terms)

record StrongResidualPolymerMembership
  (S : Support.BalabanEffectiveAction)
  (γ : Support.Polymer) : Set where
  field
    resolvedResidualTerm :
      Support.ResidualEffectiveActionTerm

    resolvedTermInEffectiveAction :
      resolvedResidualTerm ∈ResidualTerms Support.residualTerms S

    resolvedTermHasPolymer :
      Support.termPolymer resolvedResidualTerm ≡ γ

    resolvedResidualFlag :
      Support.residualAfterTransferAbsorption resolvedResidualTerm ≡ true

    resolvedSupportLinksUseResidualTerm :
      Core.AllTermUsesLinks
        (Resolver.actionTermFromResidualEffectiveActionTerm
          resolvedResidualTerm)
        (Support.supportLinks γ)

open StrongResidualPolymerMembership public

record PolymerInRefinesToStrongResidualMembership : Set₁ where
  field
    refinePolymerIn :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      Support.PolymerIn S γ →
      StrongResidualPolymerMembership S γ

open PolymerInRefinesToStrongResidualMembership public

resolvedMembershipFromStrongMembership :
  {S : Support.BalabanEffectiveAction} →
  {γ : Support.Polymer} →
  {member : Support.PolymerIn S γ} →
  StrongResidualPolymerMembership S γ →
  Obligations.ResolvedPolymerMembership S γ member
resolvedMembershipFromStrongMembership strong =
  record
    { resolvedResidualTerm =
        resolvedResidualTerm strong
    ; resolvedResidualFlag =
        resolvedResidualFlag strong
    ; resolvedSupportLinksUseResidualTerm =
        resolvedSupportLinksUseResidualTerm strong
    }

everyPolymerInResolvedResidualTermFromStrongRefinement :
  PolymerInRefinesToStrongResidualMembership →
  Obligations.EveryPolymerInHasResolvedResidualTerm
everyPolymerInResolvedResidualTermFromStrongRefinement refinement =
  record
    { resolvePolymerIn =
        λ S γ member →
          resolvedMembershipFromStrongMembership
            (refinePolymerIn refinement S γ member)
    }

record ResolvedMembershipSemanticLayerDefined : Set₂ where
  field
    residualTermListMembershipDefined :
      _∈ResidualTerms_ ≡ _∈ResidualTerms_
    strongMembershipDefined :
      StrongResidualPolymerMembership
        ≡ StrongResidualPolymerMembership
    weakToStrongRefinementDefined :
      PolymerInRefinesToStrongResidualMembership
        ≡ PolymerInRefinesToStrongResidualMembership
    resolvedMembershipAssemblyDefined :
      everyPolymerInResolvedResidualTermFromStrongRefinement
        ≡ everyPolymerInResolvedResidualTermFromStrongRefinement

resolvedMembershipSemanticLayerDefined :
  ResolvedMembershipSemanticLayerDefined
resolvedMembershipSemanticLayerDefined =
  record
    { residualTermListMembershipDefined = refl
    ; strongMembershipDefined = refl
    ; weakToStrongRefinementDefined = refl
    ; resolvedMembershipAssemblyDefined = refl
    }

resolvedMembershipSemanticLayerImplemented : Bool
resolvedMembershipSemanticLayerImplemented = true

polymerInRefinementDerivedForBalabanResidualAction : Bool
polymerInRefinementDerivedForBalabanResidualAction = false

everyPolymerInResolvedResidualTermDerivedInRepo : Bool
everyPolymerInResolvedResidualTermDerivedInRepo = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data ResolvedMembershipPromotion : Set where

resolvedMembershipPromotionImpossibleHere :
  ResolvedMembershipPromotion →
  ⊥
resolvedMembershipPromotionImpossibleHere ()

record ResolvedMembershipBoundary : Set₂ where
  field
    layerDefined :
      ResolvedMembershipSemanticLayerDefined
    layerImplemented :
      resolvedMembershipSemanticLayerImplemented ≡ true
    balabanRefinementStillOpen :
      polymerInRefinementDerivedForBalabanResidualAction ≡ false
    resolvedMembershipStillOpen :
      everyPolymerInResolvedResidualTermDerivedInRepo ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      ResolvedMembershipPromotion → ⊥

resolvedMembershipBoundary : ResolvedMembershipBoundary
resolvedMembershipBoundary =
  record
    { layerDefined = resolvedMembershipSemanticLayerDefined
    ; layerImplemented = refl
    ; balabanRefinementStillOpen = refl
    ; resolvedMembershipStillOpen = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere =
        resolvedMembershipPromotionImpossibleHere
    }
