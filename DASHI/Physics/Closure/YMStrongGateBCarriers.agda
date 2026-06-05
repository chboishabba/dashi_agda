module DASHI.Physics.Closure.YMStrongGateBCarriers where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt
  as Sprint78Temporal
import DASHI.Physics.Closure.ClaySprintSeventyOneYMMixedPlaquetteForkReceipt
  as Sprint71
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMGateBInRepoDerivationAttempts as Attempts
import DASHI.Physics.Closure.YMProviderSemanticObligations as Obligations
import DASHI.Physics.Closure.YMResolvedMembershipSemantics as Membership
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver
import DASHI.Physics.Closure.YMTemporalTransferSemanticBridge as Transfer

------------------------------------------------------------------------
-- Strong Gate-B carriers.
--
-- The current weak carriers admit counterexamples.  This module adds the two
-- missing invariants as first-class carriers instead of trying to recover them
-- from identifiers:
--
-- * transfer-matrix terms and residual terms are disjoint for each action term;
-- * polymer membership is strong residual-term membership, not a free string.

record StrongActionTermTransferResidualDisjointness : Set₁ where
  field
    transferResidualDisjoint :
      (t : Core.ActionTerm) →
      Core.TransferMatrixTerm t →
      Core.ResidualActionTerm t →
      ⊥

open StrongActionTermTransferResidualDisjointness public

strongActionTermTransferResidualDisjointnessFromSectors :
  StrongActionTermTransferResidualDisjointness
strongActionTermTransferResidualDisjointnessFromSectors =
  record
    { transferResidualDisjoint =
        Core.transferMatrixTermNotResidualBySector
    }

transferResidualExclusionSemanticsFromStrongActionCarrier :
  StrongActionTermTransferResidualDisjointness →
  Obligations.TransferResidualExclusionSemantics
transferResidualExclusionSemanticsFromStrongActionCarrier carrier =
  record
    { transferMatrixTermsExcludedFromResidual =
        transferResidualDisjoint carrier
    }

typedTemporalTransferInterpretationFromStrongActionCarrier :
  StrongActionTermTransferResidualDisjointness →
  Transfer.TypedTemporalTransferInterpretation
typedTemporalTransferInterpretationFromStrongActionCarrier carrier =
  record
    { temporalOrMixedTermAbsorbed =
        Attempts.temporalOrMixedTermAbsorbedByCurrentConstructor
    ; transferTermExcludedFromResidual =
        transferResidualDisjoint carrier
    }

receiptBackedTemporalTransferInterpretationFromStrongActionCarrier :
  StrongActionTermTransferResidualDisjointness →
  Transfer.ReceiptBackedTemporalTransferInterpretation
receiptBackedTemporalTransferInterpretationFromStrongActionCarrier carrier =
  record
    { sprint71MixedPlaquetteBookkeepingClosed = refl
    ; sprint78ConditionalReceiptSurfaceRecorded = refl
    ; typedInterpretation =
        typedTemporalTransferInterpretationFromStrongActionCarrier carrier
    }

StrongPolymerIn :
  Support.BalabanEffectiveAction →
  Support.Polymer →
  Set
StrongPolymerIn =
  Membership.StrongResidualPolymerMembership

resolvedMembershipFromStrongPolymerIn :
  {S : Support.BalabanEffectiveAction} →
  {γ : Support.Polymer} →
  StrongPolymerIn S γ →
  Obligations.ResolvedPolymerMembership S γ
    (Support.polymerIn "strong-membership-replacement")
resolvedMembershipFromStrongPolymerIn strong =
  Membership.resolvedMembershipFromStrongMembership strong

record StrongEveryPolymerInHasResolvedResidualTerm : Set₁ where
  field
    resolveStrongPolymerIn :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      StrongPolymerIn S γ →
      Obligations.ResolvedPolymerMembership S γ
        (Support.polymerIn "strong-membership-replacement")

open StrongEveryPolymerInHasResolvedResidualTerm public

strongEveryPolymerInResolvedFromStrongMembership :
  StrongEveryPolymerInHasResolvedResidualTerm
strongEveryPolymerInResolvedFromStrongMembership =
  record
    { resolveStrongPolymerIn =
        λ S γ strong →
          resolvedMembershipFromStrongPolymerIn strong
    }

spatialSupportFromStrongGateBCarriers :
  StrongActionTermTransferResidualDisjointness →
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongPolymerIn S γ →
  Support.SpatialSupport γ
spatialSupportFromStrongGateBCarriers carrier S γ strong =
  Core.allSpatialFromNoTemporalTermSupport
    noTemporal
    (Membership.StrongResidualPolymerMembership.resolvedSupportLinksUseResidualTerm
      strong)
  where
    term : Support.ResidualEffectiveActionTerm
    term =
      Membership.StrongResidualPolymerMembership.resolvedResidualTerm strong

    actionTerm : Core.ActionTerm
    actionTerm =
      Resolver.actionTermFromResidualEffectiveActionTerm term

    residual : Core.ResidualActionTerm actionTerm
    residual =
      Resolver.residualActionTermFromResidualFlag
        term
        (Membership.StrongResidualPolymerMembership.resolvedResidualFlag
          strong)

    noTemporal :
      (e : Support.Link) →
      Core.TermUsesLink actionTerm e →
      Support.TemporalLink e →
      ⊥
    noTemporal e use temporalLink =
      transferResidualDisjoint
        carrier
        actionTerm
        (Attempts.temporalOrMixedTermAbsorbedByCurrentConstructor
          actionTerm
          (Core.TemporalLinkUseClassifiesTemporalTerm.temporalLinkUseIsTemporalOrMixed
            Core.canonicalTemporalLinkUseClassifiesTemporalTerm
            actionTerm
            e
            use
            temporalLink))
        residual

record StrongEffectiveActionPolymersSpatialOnlyForA1Theorem : Set₁ where
  field
    provesSpatialSupportStrong :
      (S : Support.BalabanEffectiveAction) →
      (γ : Support.Polymer) →
      StrongPolymerIn S γ →
      Support.SpatialSupport γ

strongEffectiveActionPolymersSpatialOnlyForA1 :
  StrongActionTermTransferResidualDisjointness →
  StrongEffectiveActionPolymersSpatialOnlyForA1Theorem
strongEffectiveActionPolymersSpatialOnlyForA1 carrier =
  record
    { provesSpatialSupportStrong =
        spatialSupportFromStrongGateBCarriers carrier
    }

strongActionTermCarrierDefined : Bool
strongActionTermCarrierDefined = true

strongActionTermTransferResidualDisjointnessDerivedInRepo : Bool
strongActionTermTransferResidualDisjointnessDerivedInRepo = true

strongPolymerInReplacementDefined : Bool
strongPolymerInReplacementDefined = true

temporalAbsorptionDerivedForStrongCarrier : Bool
temporalAbsorptionDerivedForStrongCarrier = true

transferResidualExclusionRequiresStrongCarrier : Bool
transferResidualExclusionRequiresStrongCarrier = true

strongGateBSpatialSupportAssemblyDefined : Bool
strongGateBSpatialSupportAssemblyDefined = true

weakCarrierCounterexamplesStillValid : Bool
weakCarrierCounterexamplesStillValid = true

eta4EarnedUnconditionalForOldWeakGateB : Bool
eta4EarnedUnconditionalForOldWeakGateB = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data StrongGateBCarrierPromotion : Set where

strongGateBCarrierPromotionImpossibleHere :
  StrongGateBCarrierPromotion →
  ⊥
strongGateBCarrierPromotionImpossibleHere ()

record StrongGateBCarrierBoundary : Set where
  field
    actionCarrierDefined :
      strongActionTermCarrierDefined ≡ true
    actionDisjointnessDerived :
      strongActionTermTransferResidualDisjointnessDerivedInRepo ≡ true
    membershipReplacementDefined :
      strongPolymerInReplacementDefined ≡ true
    temporalAbsorptionDerived :
      temporalAbsorptionDerivedForStrongCarrier ≡ true
    transferResidualExclusionStillRequiresStrongCarrier :
      transferResidualExclusionRequiresStrongCarrier ≡ true
    strongSpatialSupportAssemblyDefined :
      strongGateBSpatialSupportAssemblyDefined ≡ true
    weakCounterexamplesPreserved :
      weakCarrierCounterexamplesStillValid ≡ true
    weakGateBEta4NotUnconditional :
      eta4EarnedUnconditionalForOldWeakGateB ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      StrongGateBCarrierPromotion → ⊥

strongGateBCarrierBoundary :
  StrongGateBCarrierBoundary
strongGateBCarrierBoundary =
  record
    { actionCarrierDefined = refl
    ; actionDisjointnessDerived = refl
    ; membershipReplacementDefined = refl
    ; temporalAbsorptionDerived = refl
    ; transferResidualExclusionStillRequiresStrongCarrier = refl
    ; strongSpatialSupportAssemblyDefined = refl
    ; weakCounterexamplesPreserved = refl
    ; weakGateBEta4NotUnconditional = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere =
        strongGateBCarrierPromotionImpossibleHere
    }
