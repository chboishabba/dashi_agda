module DASHI.Physics.Closure.YMGateBPackagingResolutionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSpatialOnlyBridge as Bridge
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMProviderDerivationInRepo as Derive
import DASHI.Physics.Closure.YMProviderSemanticObligations as Obligations
import DASHI.Physics.Closure.YMResolvedMembershipSemantics as Membership
import DASHI.Physics.Closure.YMTemporalTransferSemanticBridge as Transfer

------------------------------------------------------------------------
-- Sprint 83 Gate-B packaging-resolution boundary.
--
-- This module audits the claim that the two remaining Gate-B gaps are only
-- packaging.  Under the current in-repo types the claim is too strong:
--
-- * receipt booleans do not construct the term-level exclusion
--   TransferMatrixTerm t -> ResidualActionTerm t -> ⊥;
-- * the weak PolymerIn record is only an identifier, so finite residualTerms
--   alone does not prove list membership for a given witness.
--
-- The record below is therefore the exact stronger evidence object that would
-- make the packaging-resolution story valid without using the older Balaban
-- provider postulates.

record GateBPackagingResolutionEvidence : Set₁ where
  field
    receiptBackedTemporalTransferInterpretation :
      Transfer.ReceiptBackedTemporalTransferInterpretation

    polymerInRefinesToStrongResidualMembership :
      Membership.PolymerInRefinesToStrongResidualMembership

open GateBPackagingResolutionEvidence public

gateBSemanticObligationsFromPackagingResolution :
  GateBPackagingResolutionEvidence →
  Obligations.GateBSemanticObligations
gateBSemanticObligationsFromPackagingResolution evidence =
  record
    { temporalAbsorption =
        Transfer.temporalAbsorptionSemanticsFromReceiptBackedInterpretation
          (receiptBackedTemporalTransferInterpretation evidence)
    ; transferResidualExclusion =
        Transfer.transferResidualExclusionSemanticsFromReceiptBackedInterpretation
          (receiptBackedTemporalTransferInterpretation evidence)
    ; resolvedPolymerMembership =
        Membership.everyPolymerInResolvedResidualTermFromStrongRefinement
          (polymerInRefinesToStrongResidualMembership evidence)
    }

providerInstancesFromPackagingResolution :
  GateBPackagingResolutionEvidence →
  Derive.DerivedProviderInstancesInRepo
providerInstancesFromPackagingResolution evidence =
  Obligations.providerInstancesFromGateBSemanticObligations
    (gateBSemanticObligationsFromPackagingResolution evidence)

residualSpatialSupportEvidenceFromPackagingResolution :
  GateBPackagingResolutionEvidence →
  Bridge.ResidualEffectiveActionSpatialSupportEvidence
residualSpatialSupportEvidenceFromPackagingResolution evidence =
  Obligations.residualSpatialSupportEvidenceFromGateBSemanticObligations
    (gateBSemanticObligationsFromPackagingResolution evidence)

effectiveActionPolymersSpatialOnlyForA1FromPackagingResolution :
  GateBPackagingResolutionEvidence →
  Support.EffectiveActionPolymersSpatialOnlyForA1Theorem
effectiveActionPolymersSpatialOnlyForA1FromPackagingResolution evidence =
  Obligations.a1FromGateBSemanticObligations
    (gateBSemanticObligationsFromPackagingResolution evidence)

record GateBPackagingResolutionLayerDefined : Set₂ where
  field
    evidenceCarrierDefined :
      GateBPackagingResolutionEvidence ≡ GateBPackagingResolutionEvidence
    semanticObligationAssemblyDefined :
      gateBSemanticObligationsFromPackagingResolution
        ≡ gateBSemanticObligationsFromPackagingResolution
    providerAssemblyDefined :
      providerInstancesFromPackagingResolution
        ≡ providerInstancesFromPackagingResolution
    residualSupportAssemblyDefined :
      residualSpatialSupportEvidenceFromPackagingResolution
        ≡ residualSpatialSupportEvidenceFromPackagingResolution
    a1AssemblyDefined :
      effectiveActionPolymersSpatialOnlyForA1FromPackagingResolution
        ≡ effectiveActionPolymersSpatialOnlyForA1FromPackagingResolution

gateBPackagingResolutionLayerDefined :
  GateBPackagingResolutionLayerDefined
gateBPackagingResolutionLayerDefined =
  record
    { evidenceCarrierDefined = refl
    ; semanticObligationAssemblyDefined = refl
    ; providerAssemblyDefined = refl
    ; residualSupportAssemblyDefined = refl
    ; a1AssemblyDefined = refl
    }

gateBPackagingResolutionLayerImplemented : Bool
gateBPackagingResolutionLayerImplemented = true

receiptBooleansSufficientForTypedTemporalTransfer : Bool
receiptBooleansSufficientForTypedTemporalTransfer = false

weakPolymerInEquivalentToResidualTermListMembership : Bool
weakPolymerInEquivalentToResidualTermListMembership = false

gateBPackagingResolutionEvidenceProvidedInRepo : Bool
gateBPackagingResolutionEvidenceProvidedInRepo = false

gateBUnconditionalClosedFromPackagingResolution : Bool
gateBUnconditionalClosedFromPackagingResolution = false

eta4EarnedUnconditionalFromPackagingResolution : Bool
eta4EarnedUnconditionalFromPackagingResolution = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data GateBPackagingResolutionPromotion : Set where

gateBPackagingResolutionPromotionImpossibleHere :
  GateBPackagingResolutionPromotion →
  ⊥
gateBPackagingResolutionPromotionImpossibleHere ()

record GateBPackagingResolutionBoundary : Set₂ where
  field
    layerDefined :
      GateBPackagingResolutionLayerDefined
    layerImplemented :
      gateBPackagingResolutionLayerImplemented ≡ true
    receiptBooleansStillInsufficient :
      receiptBooleansSufficientForTypedTemporalTransfer ≡ false
    weakMembershipStillInsufficient :
      weakPolymerInEquivalentToResidualTermListMembership ≡ false
    packagingResolutionEvidenceStillMissing :
      gateBPackagingResolutionEvidenceProvidedInRepo ≡ false
    gateBStillNotUnconditional :
      gateBUnconditionalClosedFromPackagingResolution ≡ false
    eta4StillNotUnconditional :
      eta4EarnedUnconditionalFromPackagingResolution ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      GateBPackagingResolutionPromotion → ⊥

gateBPackagingResolutionBoundary :
  GateBPackagingResolutionBoundary
gateBPackagingResolutionBoundary =
  record
    { layerDefined = gateBPackagingResolutionLayerDefined
    ; layerImplemented = refl
    ; receiptBooleansStillInsufficient = refl
    ; weakMembershipStillInsufficient = refl
    ; packagingResolutionEvidenceStillMissing = refl
    ; gateBStillNotUnconditional = refl
    ; eta4StillNotUnconditional = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere =
        gateBPackagingResolutionPromotionImpossibleHere
    }
