module DASHI.Physics.Closure.YMGateBPackagingResolutionAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMBlockedL2KPEntropy as Blocked
import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMGateBPackagingResolutionBoundary as Boundary
import DASHI.Physics.Closure.YMProviderDerivationInRepo as Derive
import DASHI.Physics.Closure.YMProviderSemanticObligations as Obligations
import DASHI.Physics.Closure.YMResolvedMembershipSemantics as Membership
import DASHI.Physics.Closure.YMTemporalTransferSemanticBridge as Transfer
import DASHI.Physics.Closure.YMResidualMembershipRefinementAuthority as RefinementAuthority

------------------------------------------------------------------------
-- Sprint 83 Gate-B packaging-resolution authority.
--
-- The boundary module proves the assembly from an exact evidence bundle but
-- does not fabricate the evidence from receipt booleans.  This module supplies
-- the two remaining typed inputs as narrow authority imports:
--
-- * Sprint 71/78 interpreted over ActionTerm with transfer/residual
--   disjointness;
-- * Eriksson/Balaban finite polymer representation interpreted as a
--   weak-PolymerIn -> strong residualTerms membership refinement.
--
-- This replaces the older coarse Balaban provider postulates with a more
-- precise authority surface, but it is still authority-conditional rather than
-- an in-repo derivation.

-- The typed transfer interpretation is now derived from current sector
-- constructors and the Sprint 71/78 receipt field equalities.
sprint7178TypedTemporalTransferInterpretationAuthority :
  Transfer.ReceiptBackedTemporalTransferInterpretation
sprint7178TypedTemporalTransferInterpretationAuthority =
  Transfer.receiptBackedTemporalTransferInterpretationFromCurrentSectors

erikssonProp31PolymerInStrongResidualMembershipAuthority :
  Membership.PolymerInRefinesToStrongResidualMembership
erikssonProp31PolymerInStrongResidualMembershipAuthority =
  RefinementAuthority.erikssonProp31PolymerInStrongResidualMembershipAuthority

-- Prefer the shared refinement authority, then keep the local proof witness names
-- for backwards compatibility with this module's interface.

gateBPackagingResolutionEvidenceAuthority :
  Boundary.GateBPackagingResolutionEvidence
gateBPackagingResolutionEvidenceAuthority =
  record
    { receiptBackedTemporalTransferInterpretation =
        sprint7178TypedTemporalTransferInterpretationAuthority
    ; polymerInRefinesToStrongResidualMembership =
        erikssonProp31PolymerInStrongResidualMembershipAuthority
    }

gateBSemanticObligationsAuthorityConditional :
  Obligations.GateBSemanticObligations
gateBSemanticObligationsAuthorityConditional =
  Boundary.gateBSemanticObligationsFromPackagingResolution
    gateBPackagingResolutionEvidenceAuthority

providerInstancesAuthorityConditional :
  Derive.DerivedProviderInstancesInRepo
providerInstancesAuthorityConditional =
  Boundary.providerInstancesFromPackagingResolution
    gateBPackagingResolutionEvidenceAuthority

residualSpatialSupportEvidenceAuthorityConditional :
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
residualSpatialSupportEvidenceAuthorityConditional =
  Boundary.residualSpatialSupportEvidenceFromPackagingResolution
    gateBPackagingResolutionEvidenceAuthority

effectiveActionPolymersSpatialOnlyForA1AuthorityConditional :
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem
effectiveActionPolymersSpatialOnlyForA1AuthorityConditional =
  Boundary.effectiveActionPolymersSpatialOnlyForA1FromPackagingResolution
    gateBPackagingResolutionEvidenceAuthority

polymerDefinedOnBlockedLatticeAuthorityConditional :
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  Support.PolymerIn S γ →
  Support.DefinedOnBlockedL2SpatialGraph γ
polymerDefinedOnBlockedLatticeAuthorityConditional S γ member =
  Support.PolymerDefinedOnBlockedLatticeTheorem.provesBlockedL2SpatialGraph
    Blocked.polymerDefinedOnBlockedLatticeFromSpatialSupport
    γ
    (Support.EffectiveActionPolymersSpatialOnlyForA1Theorem.provesSpatialSupport
      effectiveActionPolymersSpatialOnlyForA1AuthorityConditional
      S
      γ
      member)

kpEntropyAtBlockedScaleL2AuthorityConditional :
  Blocked.KPEntropyAtBlockedScaleL2Theorem
kpEntropyAtBlockedScaleL2AuthorityConditional =
  Blocked.kpEntropyAtBlockedScaleL2AuthorityConditional

anisotropicL2WeightedKPClosesAuthorityConditional :
  Blocked.AnisotropicL2WeightedKPClosesAuthorityConditional
anisotropicL2WeightedKPClosesAuthorityConditional =
  Blocked.anisotropicL2WeightedKPClosesAuthorityConditional

gateBPackagingResolutionAuthorityAvailable : Bool
gateBPackagingResolutionAuthorityAvailable = true

gateBPackagingResolutionAuthorityDerivedInRepo : Bool
gateBPackagingResolutionAuthorityDerivedInRepo = false

gateBPackagingResolutionEvidenceAuthorityConditional : Bool
gateBPackagingResolutionEvidenceAuthorityConditional = true

residualSpatialSupportEvidencePackagingAuthorityConditional : Bool
residualSpatialSupportEvidencePackagingAuthorityConditional = true

effectiveActionPolymersSpatialOnlyForA1PackagingAuthorityConditional : Bool
effectiveActionPolymersSpatialOnlyForA1PackagingAuthorityConditional = true

blockedL2KPEntropyPackagingAuthorityConditional : Bool
blockedL2KPEntropyPackagingAuthorityConditional = true

allDiameterWeightedKPPackagingAuthorityConditional : Bool
allDiameterWeightedKPPackagingAuthorityConditional = true

gateBPackagingResolutionEvidenceDerivedInRepo : Bool
gateBPackagingResolutionEvidenceDerivedInRepo = false

eta4EarnedUnconditional : Bool
eta4EarnedUnconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data GateBPackagingResolutionAuthorityPromotion : Set where

gateBPackagingResolutionAuthorityPromotionImpossibleHere :
  GateBPackagingResolutionAuthorityPromotion →
  ⊥
gateBPackagingResolutionAuthorityPromotionImpossibleHere ()

record GateBPackagingResolutionAuthorityBoundary : Set where
  field
    authorityAvailable :
      gateBPackagingResolutionAuthorityAvailable ≡ true
    authorityNotDerivedInRepo :
      gateBPackagingResolutionAuthorityDerivedInRepo ≡ false
    evidenceAuthorityConditional :
      gateBPackagingResolutionEvidenceAuthorityConditional ≡ true
    residualSupportAuthorityConditional :
      residualSpatialSupportEvidencePackagingAuthorityConditional ≡ true
    a1AuthorityConditional :
      effectiveActionPolymersSpatialOnlyForA1PackagingAuthorityConditional
        ≡ true
    blockedL2KPEntropyAuthorityConditional :
      blockedL2KPEntropyPackagingAuthorityConditional ≡ true
    allDiameterKPAuthorityConditional :
      allDiameterWeightedKPPackagingAuthorityConditional ≡ true
    evidenceNotDerivedInRepo :
      gateBPackagingResolutionEvidenceDerivedInRepo ≡ false
    eta4NotUnconditional :
      eta4EarnedUnconditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      GateBPackagingResolutionAuthorityPromotion → ⊥

gateBPackagingResolutionAuthorityBoundary :
  GateBPackagingResolutionAuthorityBoundary
gateBPackagingResolutionAuthorityBoundary =
  record
    { authorityAvailable = refl
    ; authorityNotDerivedInRepo = refl
    ; evidenceAuthorityConditional = refl
    ; residualSupportAuthorityConditional = refl
    ; a1AuthorityConditional = refl
    ; blockedL2KPEntropyAuthorityConditional = refl
    ; allDiameterKPAuthorityConditional = refl
    ; evidenceNotDerivedInRepo = refl
    ; eta4NotUnconditional = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere =
        gateBPackagingResolutionAuthorityPromotionImpossibleHere
    }
