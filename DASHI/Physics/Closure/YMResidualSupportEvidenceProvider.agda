module DASHI.Physics.Closure.YMResidualSupportEvidenceProvider where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver

------------------------------------------------------------------------
-- Evidence provider assembly.
--
-- This module provides the missing proof plumbing requested after Sprint 82:
-- once transfer/residual disjointness for temporal terms and a residual-term
-- membership resolver are supplied, all four evidence objects are assembled.
-- The Balaban-specific instances of those two inputs remain the honest proof
-- obligations.

record TemporalTransferResidualDisjointnessProvider : Set₁ where
  field
    temporalTermIsTransferMatrixTerm :
      (t : Core.ActionTerm) →
      Core.TemporalOrMixedTerm t →
      Core.TransferMatrixTerm t

    transferMatrixTermNotResidual :
      (t : Core.ActionTerm) →
      Core.TransferMatrixTerm t →
      Core.ResidualActionTerm t →
      ⊥

open TemporalTransferResidualDisjointnessProvider public

temporalTermAbsorbedNotResidualEvidenceFromProvider :
  TemporalTransferResidualDisjointnessProvider →
  Core.TemporalTermAbsorbedNotResidualEvidence
temporalTermAbsorbedNotResidualEvidenceFromProvider provider =
  record
    { temporalTermIsTransferMatrixTerm =
        temporalTermIsTransferMatrixTerm provider
    ; transferMatrixTermNotResidual =
        transferMatrixTermNotResidual provider
    }

residualTermHasNoTemporalSupportEvidenceFromProvider :
  TemporalTransferResidualDisjointnessProvider →
  Core.ResidualTermHasNoTemporalSupportEvidence
residualTermHasNoTemporalSupportEvidenceFromProvider provider =
  Core.residualTermHasNoTemporalSupportFromAbsorption
    (temporalTermAbsorbedNotResidualEvidenceFromProvider provider)
    Core.canonicalTemporalLinkUseClassifiesTemporalTerm

residualPolymerTermSupportSemanticsFromResolverProvider :
  Resolver.PolymerInResidualTermResolver →
  Core.ResidualPolymerTermSupportSemantics
residualPolymerTermSupportSemanticsFromResolverProvider =
  Resolver.residualPolymerTermSupportSemanticsFromResolver

residualEffectiveActionSpatialSupportEvidenceFromProviders :
  TemporalTransferResidualDisjointnessProvider →
  Resolver.PolymerInResidualTermResolver →
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
residualEffectiveActionSpatialSupportEvidenceFromProviders provider resolver =
  Core.residualSpatialSupportEvidenceFromTermNoTemporal
    (residualTermHasNoTemporalSupportEvidenceFromProvider provider)
    (residualPolymerTermSupportSemanticsFromResolverProvider resolver)

effectiveActionPolymersSpatialOnlyForA1FromProviders :
  TemporalTransferResidualDisjointnessProvider →
  Resolver.PolymerInResidualTermResolver →
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem
effectiveActionPolymersSpatialOnlyForA1FromProviders provider resolver =
  Bridge.effectiveActionPolymersSpatialOnlyForA1FromEvidence
    (residualEffectiveActionSpatialSupportEvidenceFromProviders provider resolver)

record ResidualSupportEvidenceProviderLayerDefined : Set₂ where
  field
    disjointnessProviderDefined :
      TemporalTransferResidualDisjointnessProvider
        ≡ TemporalTransferResidualDisjointnessProvider
    temporalAbsorptionEvidenceAssemblyDefined :
      temporalTermAbsorbedNotResidualEvidenceFromProvider
        ≡ temporalTermAbsorbedNotResidualEvidenceFromProvider
    temporalClassifierProvided :
      Core.temporalLinkUseClassifiesTemporalTermProved ≡ true
    residualNoTemporalAssemblyDefined :
      residualTermHasNoTemporalSupportEvidenceFromProvider
        ≡ residualTermHasNoTemporalSupportEvidenceFromProvider
    resolverToSemanticsAssemblyDefined :
      residualPolymerTermSupportSemanticsFromResolverProvider
        ≡ residualPolymerTermSupportSemanticsFromResolverProvider
    residualSpatialEvidenceAssemblyDefined :
      residualEffectiveActionSpatialSupportEvidenceFromProviders
        ≡ residualEffectiveActionSpatialSupportEvidenceFromProviders

residualSupportEvidenceProviderLayerDefined :
  ResidualSupportEvidenceProviderLayerDefined
residualSupportEvidenceProviderLayerDefined =
  record
    { disjointnessProviderDefined = refl
    ; temporalAbsorptionEvidenceAssemblyDefined = refl
    ; temporalClassifierProvided = refl
    ; residualNoTemporalAssemblyDefined = refl
    ; resolverToSemanticsAssemblyDefined = refl
    ; residualSpatialEvidenceAssemblyDefined = refl
    }

temporalTransferResidualDisjointnessProvedForBalaban : Bool
temporalTransferResidualDisjointnessProvedForBalaban = false

balabanResidualMembershipResolverProved : Bool
balabanResidualMembershipResolverProved =
  Resolver.polymerInResidualTermResolverProvedForBalabanEffectiveAction

residualEffectiveActionSpatialSupportEvidenceProvedForBalaban : Bool
residualEffectiveActionSpatialSupportEvidenceProvedForBalaban = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data EvidenceProviderPromotion : Set where

evidenceProviderPromotionImpossibleHere :
  EvidenceProviderPromotion →
  ⊥
evidenceProviderPromotionImpossibleHere ()

record ResidualSupportEvidenceProviderBoundary : Set₂ where
  field
    providerLayerDefined :
      ResidualSupportEvidenceProviderLayerDefined
    temporalDisjointnessStillOpen :
      temporalTransferResidualDisjointnessProvedForBalaban ≡ false
    balabanResolverStillOpen :
      balabanResidualMembershipResolverProved ≡ false
    residualSpatialEvidenceStillOpen :
      residualEffectiveActionSpatialSupportEvidenceProvedForBalaban ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      EvidenceProviderPromotion → ⊥

residualSupportEvidenceProviderBoundary :
  ResidualSupportEvidenceProviderBoundary
residualSupportEvidenceProviderBoundary =
  record
    { providerLayerDefined = residualSupportEvidenceProviderLayerDefined
    ; temporalDisjointnessStillOpen = refl
    ; balabanResolverStillOpen = refl
    ; residualSpatialEvidenceStillOpen = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = evidenceProviderPromotionImpossibleHere
    }
