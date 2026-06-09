module DASHI.Physics.Closure.YMProviderDerivationInRepo where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMResidualSupportEvidenceProvider as Provider
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver

------------------------------------------------------------------------
-- In-repo provider derivation surface.
--
-- The downstream Gate-B proof now only needs two provider instances:
--
--   1. temporal/mixed transfer terms are disjoint from residual terms;
--   2. a PolymerIn witness resolves to the residual term whose term-use
--      links are exactly the polymer support links.
--
-- This module supplies constructive derivation functions for both providers
-- from explicit semantic inputs.  It deliberately does not postulate Balaban
-- instances and does not claim that the current weak PolymerIn relation
-- already contains the data needed to build those inputs.

record TemporalTransferResidualDisjointnessSemantics : Set₁ where
  field
    temporalOrMixedTermAbsorbedIntoTransferMatrix :
      (t : Core.ActionTerm) →
      Core.TemporalOrMixedTerm t →
      Core.TransferMatrixTerm t

    transferMatrixTermsExcludedFromResidual :
      (t : Core.ActionTerm) →
      Core.TransferMatrixTerm t →
      Core.ResidualActionTerm t →
      ⊥

open TemporalTransferResidualDisjointnessSemantics public

deriveTemporalTransferResidualDisjointnessProviderInRepo :
  TemporalTransferResidualDisjointnessSemantics →
  Provider.TemporalTransferResidualDisjointnessProvider
deriveTemporalTransferResidualDisjointnessProviderInRepo semantics =
  record
    { temporalTermIsTransferMatrixTerm =
        temporalOrMixedTermAbsorbedIntoTransferMatrix semantics
    ; transferMatrixTermNotResidual =
        transferMatrixTermsExcludedFromResidual semantics
    }

record ResidualMembershipSemantics : Set₁ where
  field
    residualTermForMembership :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      Support.PolymerIn S γ →
      Support.ResidualEffectiveActionTerm

    residualTermForMembershipCarriesResidualFlag :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      (member : Support.PolymerIn S γ) →
      Support.residualAfterTransferAbsorption
        (residualTermForMembership S γ member)
        ≡ true

    supportLinksAreUsesOfResolvedResidualTerm :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      (member : Support.PolymerIn S γ) →
      Core.AllTermUsesLinks
        (Resolver.actionTermFromResidualEffectiveActionTerm
          (residualTermForMembership S γ member))
        (Support.supportLinks γ)

open ResidualMembershipSemantics public

derivePolymerInResidualTermResolverInRepo :
  ResidualMembershipSemantics →
  Resolver.PolymerInResidualTermResolver
derivePolymerInResidualTermResolverInRepo semantics =
  record
    { residualTermForMembership =
        residualTermForMembership semantics
    ; residualTermForMembershipIsResidual =
        residualTermForMembershipCarriesResidualFlag semantics
    ; membershipSupportLinksUseResidualTerm =
        supportLinksAreUsesOfResolvedResidualTerm semantics
    }

record DerivedProviderInstancesInRepo : Set₁ where
  field
    temporalDisjointnessSemantics :
      TemporalTransferResidualDisjointnessSemantics
    residualMembershipSemantics :
      ResidualMembershipSemantics

open DerivedProviderInstancesInRepo public

derivedTemporalTransferResidualDisjointnessProviderInRepo :
  DerivedProviderInstancesInRepo →
  Provider.TemporalTransferResidualDisjointnessProvider
derivedTemporalTransferResidualDisjointnessProviderInRepo derived =
  deriveTemporalTransferResidualDisjointnessProviderInRepo
    (temporalDisjointnessSemantics derived)

derivedPolymerInResidualTermResolverInRepo :
  DerivedProviderInstancesInRepo →
  Resolver.PolymerInResidualTermResolver
derivedPolymerInResidualTermResolverInRepo derived =
  derivePolymerInResidualTermResolverInRepo
    (residualMembershipSemantics derived)

derivedResidualEffectiveActionSpatialSupportEvidenceInRepo :
  DerivedProviderInstancesInRepo →
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
derivedResidualEffectiveActionSpatialSupportEvidenceInRepo derived =
  Provider.residualEffectiveActionSpatialSupportEvidenceFromProviders
    (derivedTemporalTransferResidualDisjointnessProviderInRepo derived)
    (derivedPolymerInResidualTermResolverInRepo derived)

derivedEffectiveActionPolymersSpatialOnlyForA1InRepo :
  DerivedProviderInstancesInRepo →
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem
derivedEffectiveActionPolymersSpatialOnlyForA1InRepo derived =
  Provider.effectiveActionPolymersSpatialOnlyForA1FromProviders
    (derivedTemporalTransferResidualDisjointnessProviderInRepo derived)
    (derivedPolymerInResidualTermResolverInRepo derived)

record ProviderDerivationLayerDefined : Set₂ where
  field
    temporalDisjointnessSemanticsDefined :
      TemporalTransferResidualDisjointnessSemantics
        ≡ TemporalTransferResidualDisjointnessSemantics
    temporalDisjointnessProviderDerivationDefined :
      deriveTemporalTransferResidualDisjointnessProviderInRepo
        ≡ deriveTemporalTransferResidualDisjointnessProviderInRepo
    residualMembershipSemanticsDefined :
      ResidualMembershipSemantics ≡ ResidualMembershipSemantics
    residualMembershipResolverDerivationDefined :
      derivePolymerInResidualTermResolverInRepo
        ≡ derivePolymerInResidualTermResolverInRepo
    providerBundleDefined :
      DerivedProviderInstancesInRepo ≡ DerivedProviderInstancesInRepo
    residualSpatialEvidenceDerivationDefined :
      derivedResidualEffectiveActionSpatialSupportEvidenceInRepo
        ≡ derivedResidualEffectiveActionSpatialSupportEvidenceInRepo
    a1DerivationDefined :
      derivedEffectiveActionPolymersSpatialOnlyForA1InRepo
        ≡ derivedEffectiveActionPolymersSpatialOnlyForA1InRepo

providerDerivationLayerDefined : ProviderDerivationLayerDefined
providerDerivationLayerDefined =
  record
    { temporalDisjointnessSemanticsDefined = refl
    ; temporalDisjointnessProviderDerivationDefined = refl
    ; residualMembershipSemanticsDefined = refl
    ; residualMembershipResolverDerivationDefined = refl
    ; providerBundleDefined = refl
    ; residualSpatialEvidenceDerivationDefined = refl
    ; a1DerivationDefined = refl
    }

providerDerivationLayerImplemented : Bool
providerDerivationLayerImplemented = true

temporalTransferResidualDisjointnessSemanticsDerivedInRepo : Bool
temporalTransferResidualDisjointnessSemanticsDerivedInRepo = false

residualMembershipSemanticsDerivedInRepo : Bool
residualMembershipSemanticsDerivedInRepo = false

providerInstancesDerivedInRepo : Bool
providerInstancesDerivedInRepo = false

residualSpatialSupportEvidenceDerivedInRepo : Bool
residualSpatialSupportEvidenceDerivedInRepo = false

effectiveActionPolymersSpatialOnlyForA1DerivedInRepo : Bool
effectiveActionPolymersSpatialOnlyForA1DerivedInRepo = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data ProviderDerivationPromotion : Set where

providerDerivationPromotionImpossibleHere :
  ProviderDerivationPromotion →
  ⊥
providerDerivationPromotionImpossibleHere ()

record ProviderDerivationBoundary : Set₂ where
  field
    derivationLayerDefined :
      ProviderDerivationLayerDefined
    constructorsImplemented :
      providerDerivationLayerImplemented ≡ true
    temporalDisjointnessSemanticsStillOpen :
      temporalTransferResidualDisjointnessSemanticsDerivedInRepo ≡ false
    residualMembershipSemanticsStillOpen :
      residualMembershipSemanticsDerivedInRepo ≡ false
    providersStillNotDerived :
      providerInstancesDerivedInRepo ≡ false
    residualSpatialSupportStillNotDerived :
      residualSpatialSupportEvidenceDerivedInRepo ≡ false
    a1StillNotDerived :
      effectiveActionPolymersSpatialOnlyForA1DerivedInRepo ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      ProviderDerivationPromotion → ⊥

providerDerivationBoundary : ProviderDerivationBoundary
providerDerivationBoundary =
  record
    { derivationLayerDefined = providerDerivationLayerDefined
    ; constructorsImplemented = refl
    ; temporalDisjointnessSemanticsStillOpen = refl
    ; residualMembershipSemanticsStillOpen = refl
    ; providersStillNotDerived = refl
    ; residualSpatialSupportStillNotDerived = refl
    ; a1StillNotDerived = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = providerDerivationPromotionImpossibleHere
    }
