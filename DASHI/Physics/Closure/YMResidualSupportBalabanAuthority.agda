module DASHI.Physics.Closure.YMResidualSupportBalabanAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMResidualSupportEvidenceProvider as Provider
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver
import DASHI.Physics.Closure.YMResidualMembershipRefinementAuthority as RefinementAuthority

------------------------------------------------------------------------
-- Balaban-specific authority surface for the Sprint 82 provider layer.
--
-- Current in-repo receipts package transfer absorption and residual support as
-- booleans/strings.  They do not directly provide the term-level resolver
-- for `PolymerIn` witnesses, so this module keeps one explicit Balaban authority
-- assumption there.  The temporal transfer/residual disjointness witness is
-- derived directly from the existing sector-typed core.

balabanTemporalTransferResidualDisjointnessProvider :
  Provider.TemporalTransferResidualDisjointnessProvider
balabanTemporalTransferResidualDisjointnessProvider =
  record
    { temporalTermIsTransferMatrixTerm =
        λ t temporal → Core.transferMatrixTerm
          (Core.TemporalOrMixedTerm.temporalOrMixedIsTransfer temporal)
    ; transferMatrixTermNotResidual =
        Core.transferMatrixTermNotResidualBySector
    }

balabanPolymerInResidualTermResolver :
  Resolver.PolymerInResidualTermResolver
balabanPolymerInResidualTermResolver =
  RefinementAuthority.balabanPolymerInResidualTermResolverAuthority

balabanResidualEffectiveActionSpatialSupportEvidence :
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
balabanResidualEffectiveActionSpatialSupportEvidence =
  Provider.residualEffectiveActionSpatialSupportEvidenceFromProviders
    balabanTemporalTransferResidualDisjointnessProvider
    balabanPolymerInResidualTermResolver

balabanEffectiveActionPolymersSpatialOnlyForA1 :
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem
balabanEffectiveActionPolymersSpatialOnlyForA1 =
  Provider.effectiveActionPolymersSpatialOnlyForA1FromProviders
    balabanTemporalTransferResidualDisjointnessProvider
    balabanPolymerInResidualTermResolver

balabanProviderAuthorityAvailable : Bool
balabanProviderAuthorityAvailable = true

balabanProviderAuthorityDerivedInRepo : Bool
balabanProviderAuthorityDerivedInRepo = false

balabanResidualSpatialSupportEvidenceAuthorityConditional : Bool
balabanResidualSpatialSupportEvidenceAuthorityConditional = true

balabanResidualSpatialSupportEvidenceUnconditional : Bool
balabanResidualSpatialSupportEvidenceUnconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data BalabanAuthorityPromotion : Set where

balabanAuthorityPromotionImpossibleHere :
  BalabanAuthorityPromotion →
  ⊥
balabanAuthorityPromotionImpossibleHere ()

record BalabanResidualSupportAuthorityBoundary : Set where
  field
    authorityAvailable :
      balabanProviderAuthorityAvailable ≡ true
    authorityNotDerivedInRepo :
      balabanProviderAuthorityDerivedInRepo ≡ false
    residualSupportEvidenceAuthorityConditional :
      balabanResidualSpatialSupportEvidenceAuthorityConditional ≡ true
    residualSupportEvidenceNotUnconditional :
      balabanResidualSpatialSupportEvidenceUnconditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      BalabanAuthorityPromotion → ⊥

balabanResidualSupportAuthorityBoundary :
  BalabanResidualSupportAuthorityBoundary
balabanResidualSupportAuthorityBoundary =
  record
    { authorityAvailable = refl
    ; authorityNotDerivedInRepo = refl
    ; residualSupportEvidenceAuthorityConditional = refl
    ; residualSupportEvidenceNotUnconditional = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = balabanAuthorityPromotionImpossibleHere
    }
