module DASHI.Physics.Closure.YMProviderSemanticObligations where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMProviderDerivationInRepo as Derive
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMResidualSupportEvidenceProvider as Provider
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver

------------------------------------------------------------------------
-- Semantic subobligations below the provider derivation layer.
--
-- YMProviderDerivationInRepo showed that Gate B no longer lacks provider
-- constructors.  This module splits the remaining semantic inputs into the
-- exact typed facts that must be derived from the Balaban/transfer machinery.

record TemporalAbsorptionSemantics : Set₁ where
  field
    temporalOrMixedTermAbsorbedIntoTransferMatrix :
      (t : Core.ActionTerm) →
      Core.TemporalOrMixedTerm t →
      Core.TransferMatrixTerm t

open TemporalAbsorptionSemantics public

record TransferResidualExclusionSemantics : Set₁ where
  field
    transferMatrixTermsExcludedFromResidual :
      (t : Core.ActionTerm) →
      Core.TransferMatrixTerm t →
      Core.ResidualActionTerm t →
      ⊥

open TransferResidualExclusionSemantics public

temporalTransferResidualDisjointnessSemanticsFromParts :
  TemporalAbsorptionSemantics →
  TransferResidualExclusionSemantics →
  Derive.TemporalTransferResidualDisjointnessSemantics
temporalTransferResidualDisjointnessSemanticsFromParts absorption exclusion =
  record
    { temporalOrMixedTermAbsorbedIntoTransferMatrix =
        temporalOrMixedTermAbsorbedIntoTransferMatrix absorption
    ; transferMatrixTermsExcludedFromResidual =
        transferMatrixTermsExcludedFromResidual exclusion
    }

record ResolvedPolymerMembership
  (S : Support.BalabanEffectiveAction)
  (γ : Support.Polymer)
  (member : Support.PolymerIn S γ) : Set where
  field
    resolvedResidualTerm :
      Support.ResidualEffectiveActionTerm

    resolvedResidualFlag :
      Support.residualAfterTransferAbsorption resolvedResidualTerm ≡ true

    resolvedSupportLinksUseResidualTerm :
      Core.AllTermUsesLinks
        (Resolver.actionTermFromResidualEffectiveActionTerm
          resolvedResidualTerm)
        (Support.supportLinks γ)

open ResolvedPolymerMembership public

record EveryPolymerInHasResolvedResidualTerm : Set₁ where
  field
    resolvePolymerIn :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      (member : Support.PolymerIn S γ) →
      ResolvedPolymerMembership S γ member

open EveryPolymerInHasResolvedResidualTerm public

residualMembershipSemanticsFromResolvedMembership :
  EveryPolymerInHasResolvedResidualTerm →
  Derive.ResidualMembershipSemantics
residualMembershipSemanticsFromResolvedMembership resolved =
  record
    { residualTermForMembership =
        λ S γ member →
          resolvedResidualTerm
            (resolvePolymerIn resolved S γ member)
    ; residualTermForMembershipCarriesResidualFlag =
        λ S γ member →
          resolvedResidualFlag
            (resolvePolymerIn resolved S γ member)
    ; supportLinksAreUsesOfResolvedResidualTerm =
        λ S γ member →
          resolvedSupportLinksUseResidualTerm
            (resolvePolymerIn resolved S γ member)
    }

record GateBSemanticObligations : Set₁ where
  field
    temporalAbsorption :
      TemporalAbsorptionSemantics
    transferResidualExclusion :
      TransferResidualExclusionSemantics
    resolvedPolymerMembership :
      EveryPolymerInHasResolvedResidualTerm

open GateBSemanticObligations public

providerInstancesFromGateBSemanticObligations :
  GateBSemanticObligations →
  Derive.DerivedProviderInstancesInRepo
providerInstancesFromGateBSemanticObligations obligations =
  record
    { temporalDisjointnessSemantics =
        temporalTransferResidualDisjointnessSemanticsFromParts
          (temporalAbsorption obligations)
          (transferResidualExclusion obligations)
    ; residualMembershipSemantics =
        residualMembershipSemanticsFromResolvedMembership
          (resolvedPolymerMembership obligations)
    }

residualSpatialSupportEvidenceFromGateBSemanticObligations :
  GateBSemanticObligations →
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
residualSpatialSupportEvidenceFromGateBSemanticObligations obligations =
  Derive.derivedResidualEffectiveActionSpatialSupportEvidenceInRepo
    (providerInstancesFromGateBSemanticObligations obligations)

a1FromGateBSemanticObligations :
  GateBSemanticObligations →
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem
a1FromGateBSemanticObligations obligations =
  Derive.derivedEffectiveActionPolymersSpatialOnlyForA1InRepo
    (providerInstancesFromGateBSemanticObligations obligations)

record SemanticObligationLayerDefined : Set₂ where
  field
    temporalAbsorptionSemanticsDefined :
      TemporalAbsorptionSemantics ≡ TemporalAbsorptionSemantics
    transferResidualExclusionSemanticsDefined :
      TransferResidualExclusionSemantics
        ≡ TransferResidualExclusionSemantics
    temporalDisjointnessSemanticsAssemblyDefined :
      temporalTransferResidualDisjointnessSemanticsFromParts
        ≡ temporalTransferResidualDisjointnessSemanticsFromParts
    resolvedMembershipDefined :
      ResolvedPolymerMembership ≡ ResolvedPolymerMembership
    everyPolymerInResolvedDefined :
      EveryPolymerInHasResolvedResidualTerm
        ≡ EveryPolymerInHasResolvedResidualTerm
    residualMembershipSemanticsAssemblyDefined :
      residualMembershipSemanticsFromResolvedMembership
        ≡ residualMembershipSemanticsFromResolvedMembership
    gateBObligationBundleDefined :
      GateBSemanticObligations ≡ GateBSemanticObligations
    providerInstancesAssemblyDefined :
      providerInstancesFromGateBSemanticObligations
        ≡ providerInstancesFromGateBSemanticObligations
    residualSpatialSupportAssemblyDefined :
      residualSpatialSupportEvidenceFromGateBSemanticObligations
        ≡ residualSpatialSupportEvidenceFromGateBSemanticObligations
    a1AssemblyDefined :
      a1FromGateBSemanticObligations
        ≡ a1FromGateBSemanticObligations

semanticObligationLayerDefined : SemanticObligationLayerDefined
semanticObligationLayerDefined =
  record
    { temporalAbsorptionSemanticsDefined = refl
    ; transferResidualExclusionSemanticsDefined = refl
    ; temporalDisjointnessSemanticsAssemblyDefined = refl
    ; resolvedMembershipDefined = refl
    ; everyPolymerInResolvedDefined = refl
    ; residualMembershipSemanticsAssemblyDefined = refl
    ; gateBObligationBundleDefined = refl
    ; providerInstancesAssemblyDefined = refl
    ; residualSpatialSupportAssemblyDefined = refl
    ; a1AssemblyDefined = refl
    }

semanticObligationLayerImplemented : Bool
semanticObligationLayerImplemented = true

temporalAbsorptionSemanticsDerivedFromReceipts : Bool
temporalAbsorptionSemanticsDerivedFromReceipts = false

transferResidualExclusionSemanticsDerivedFromReceipts : Bool
transferResidualExclusionSemanticsDerivedFromReceipts = false

everyPolymerInResolvedResidualTermDerivedFromCurrentPolymerIn : Bool
everyPolymerInResolvedResidualTermDerivedFromCurrentPolymerIn = false

gateBSemanticObligationsDerivedInRepo : Bool
gateBSemanticObligationsDerivedInRepo = false

residualSpatialSupportEvidenceDerivedFromSemanticObligations : Bool
residualSpatialSupportEvidenceDerivedFromSemanticObligations = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data SemanticObligationPromotion : Set where

semanticObligationPromotionImpossibleHere :
  SemanticObligationPromotion →
  ⊥
semanticObligationPromotionImpossibleHere ()

record SemanticObligationBoundary : Set₂ where
  field
    layerDefined :
      SemanticObligationLayerDefined
    layerImplemented :
      semanticObligationLayerImplemented ≡ true
    temporalAbsorptionStillOpen :
      temporalAbsorptionSemanticsDerivedFromReceipts ≡ false
    transferResidualExclusionStillOpen :
      transferResidualExclusionSemanticsDerivedFromReceipts ≡ false
    currentPolymerInResolverStillOpen :
      everyPolymerInResolvedResidualTermDerivedFromCurrentPolymerIn ≡ false
    semanticObligationsStillOpen :
      gateBSemanticObligationsDerivedInRepo ≡ false
    residualSpatialSupportStillOpen :
      residualSpatialSupportEvidenceDerivedFromSemanticObligations ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      SemanticObligationPromotion → ⊥

semanticObligationBoundary : SemanticObligationBoundary
semanticObligationBoundary =
  record
    { layerDefined = semanticObligationLayerDefined
    ; layerImplemented = refl
    ; temporalAbsorptionStillOpen = refl
    ; transferResidualExclusionStillOpen = refl
    ; currentPolymerInResolverStillOpen = refl
    ; semanticObligationsStillOpen = refl
    ; residualSpatialSupportStillOpen = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = semanticObligationPromotionImpossibleHere
    }
