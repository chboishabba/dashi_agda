module DASHI.Physics.Closure.YMTemporalTransferSemanticBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt
  as Sprint78Temporal
import DASHI.Physics.Closure.ClaySprintSeventyOneYMMixedPlaquetteForkReceipt
  as Sprint71
import DASHI.Physics.Closure.YMProviderSemanticObligations as Obligations
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core

------------------------------------------------------------------------
-- Typed transfer semantics bridge.
--
-- Sprint 71/78 receipts record the corrected transfer bookkeeping at Boolean
-- receipt level.  Gate B needs typed functions over ActionTerm.  This module
-- records exactly the extra interpretation layer required to convert those
-- receipts into TemporalAbsorptionSemantics and
-- TransferResidualExclusionSemantics.

record TypedTemporalTransferInterpretation : Set₁ where
  field
    temporalOrMixedTermAbsorbed :
      (t : Core.ActionTerm) →
      Core.TemporalOrMixedTerm t →
      Core.TransferMatrixTerm t

    transferTermExcludedFromResidual :
      (t : Core.ActionTerm) →
      Core.TransferMatrixTerm t →
      Core.ResidualActionTerm t →
      ⊥

open TypedTemporalTransferInterpretation public

record ReceiptBackedTemporalTransferInterpretation : Set₁ where
  field
    sprint71MixedPlaquetteBookkeepingClosed :
      Sprint71.ClaySprintSeventyOneYMMixedPlaquetteForkReceipt.mixedPlaquettesAreTransferMatrixNotCorrection
        Sprint71.canonicalSprint71YMMixedPlaquetteForkReceipt
        ≡ true

    sprint78ConditionalReceiptSurfaceRecorded :
      Sprint78Temporal.ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt.conditionalReceiptSurface
        Sprint78Temporal.canonicalSprint78YMTemporalTermsAbsorbedReceipt
        ≡ true

    typedInterpretation :
      TypedTemporalTransferInterpretation

open ReceiptBackedTemporalTransferInterpretation public

-- Current-sector constructive witness: temporal/ mixed terms are always tagged
-- as transfer-matrix terms by sector, and transfer terms are excluded from
-- residual sector.
temporalTransferInterpretationFromCurrentSectors :
  TypedTemporalTransferInterpretation
temporalTransferInterpretationFromCurrentSectors =
  record
    { temporalOrMixedTermAbsorbed =
        λ t temporal →
          Core.transferMatrixTerm
            (Core.TemporalOrMixedTerm.temporalOrMixedIsTransfer temporal)
    ; transferTermExcludedFromResidual =
        Core.transferMatrixTermNotResidualBySector
    }

receiptBackedTemporalTransferInterpretationFromCurrentSectors :
  ReceiptBackedTemporalTransferInterpretation
receiptBackedTemporalTransferInterpretationFromCurrentSectors =
  record
    { sprint71MixedPlaquetteBookkeepingClosed = refl
    ; sprint78ConditionalReceiptSurfaceRecorded = refl
    ; typedInterpretation = temporalTransferInterpretationFromCurrentSectors
    }

temporalAbsorptionSemanticsFromReceiptBackedInterpretation :
  ReceiptBackedTemporalTransferInterpretation →
  Obligations.TemporalAbsorptionSemantics
temporalAbsorptionSemanticsFromReceiptBackedInterpretation backed =
  record
    { temporalOrMixedTermAbsorbedIntoTransferMatrix =
        temporalOrMixedTermAbsorbed
          (typedInterpretation backed)
    }

transferResidualExclusionSemanticsFromReceiptBackedInterpretation :
  ReceiptBackedTemporalTransferInterpretation →
  Obligations.TransferResidualExclusionSemantics
transferResidualExclusionSemanticsFromReceiptBackedInterpretation backed =
  record
    { transferMatrixTermsExcludedFromResidual =
        transferTermExcludedFromResidual
          (typedInterpretation backed)
    }

record TemporalTransferSemanticBridgeDefined : Set₂ where
  field
    typedInterpretationDefined :
      TypedTemporalTransferInterpretation
        ≡ TypedTemporalTransferInterpretation
    receiptBackedInterpretationDefined :
      ReceiptBackedTemporalTransferInterpretation
        ≡ ReceiptBackedTemporalTransferInterpretation
    temporalAbsorptionAssemblyDefined :
      temporalAbsorptionSemanticsFromReceiptBackedInterpretation
        ≡ temporalAbsorptionSemanticsFromReceiptBackedInterpretation
    transferResidualExclusionAssemblyDefined :
      transferResidualExclusionSemanticsFromReceiptBackedInterpretation
        ≡ transferResidualExclusionSemanticsFromReceiptBackedInterpretation

temporalTransferSemanticBridgeDefined :
  TemporalTransferSemanticBridgeDefined
temporalTransferSemanticBridgeDefined =
  record
    { typedInterpretationDefined = refl
    ; receiptBackedInterpretationDefined = refl
    ; temporalAbsorptionAssemblyDefined = refl
    ; transferResidualExclusionAssemblyDefined = refl
    }

temporalTransferSemanticBridgeImplemented : Bool
temporalTransferSemanticBridgeImplemented = true

typedTemporalTransferInterpretationDerivedInRepo : Bool
typedTemporalTransferInterpretationDerivedInRepo = true

temporalAbsorptionSemanticsDerivedInRepo : Bool
temporalAbsorptionSemanticsDerivedInRepo = true

transferResidualExclusionSemanticsDerivedInRepo : Bool
transferResidualExclusionSemanticsDerivedInRepo = true

temporalAbsorptionSemanticsFromCurrentSectors :
  Obligations.TemporalAbsorptionSemantics
temporalAbsorptionSemanticsFromCurrentSectors =
  temporalAbsorptionSemanticsFromReceiptBackedInterpretation
    receiptBackedTemporalTransferInterpretationFromCurrentSectors

transferResidualExclusionSemanticsFromCurrentSectors :
  Obligations.TransferResidualExclusionSemantics
transferResidualExclusionSemanticsFromCurrentSectors =
  transferResidualExclusionSemanticsFromReceiptBackedInterpretation
    receiptBackedTemporalTransferInterpretationFromCurrentSectors

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data TemporalTransferSemanticPromotion : Set where

temporalTransferSemanticPromotionImpossibleHere :
  TemporalTransferSemanticPromotion →
  ⊥
temporalTransferSemanticPromotionImpossibleHere ()

record TemporalTransferSemanticBoundary : Set₂ where
  field
    bridgeDefined :
      TemporalTransferSemanticBridgeDefined
    bridgeImplemented :
      temporalTransferSemanticBridgeImplemented ≡ true
    typedInterpretationIsDerived :
      typedTemporalTransferInterpretationDerivedInRepo ≡ true
    temporalAbsorptionIsDerived :
      temporalAbsorptionSemanticsDerivedInRepo ≡ true
    transferResidualExclusionIsDerived :
      transferResidualExclusionSemanticsDerivedInRepo ≡ true
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      TemporalTransferSemanticPromotion → ⊥

temporalTransferSemanticBoundary : TemporalTransferSemanticBoundary
temporalTransferSemanticBoundary =
  record
    { bridgeDefined = temporalTransferSemanticBridgeDefined
    ; bridgeImplemented = refl
    ; typedInterpretationIsDerived = refl
    ; temporalAbsorptionIsDerived = refl
    ; transferResidualExclusionIsDerived = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere =
        temporalTransferSemanticPromotionImpossibleHere
    }
