module DASHI.Physics.Closure.PolymerKPAsMDLReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MDLFejerAxiomsShift as Fejer
import DASHI.Physics.Closure.StrongCouplingExpansionReceipt as Strong
import DASHI.Physics.Closure.UniformBoundStrongCouplingReceipt as Uniform

------------------------------------------------------------------------
-- Polymer/Kotecky-Preiss as MDL bookkeeping receipt.
--
-- This receipt records only the formal analogy requested by the external
-- proof-claim intake: polymer activity control has the same bookkeeping
-- shape as MDL/Fejer descent.  It consumes existing DASHI MDL and finite
-- strong-coupling receipts, but it does not prove a continuum polymer
-- expansion, a Kotecky-Preiss condition, or a Clay Yang-Mills theorem.

data PolymerKPAsMDLStatus : Set where
  polymerKPShapeRecordedViaMDLFejerOnly :
    PolymerKPAsMDLStatus

data PolymerKPAsMDLSurface : Set where
  polymerActivityDescriptionLength :
    PolymerKPAsMDLSurface

  koteckyPreissLocalSumBound :
    PolymerKPAsMDLSurface

  uniformVolumeKoteckyPreissObligation :
    PolymerKPAsMDLSurface

  mdlFejerDescentBookkeeping :
    PolymerKPAsMDLSurface

  finiteStrongCouplingClusterExpansion :
    PolymerKPAsMDLSurface

canonicalPolymerKPAsMDLSurfaces : List PolymerKPAsMDLSurface
canonicalPolymerKPAsMDLSurfaces =
  polymerActivityDescriptionLength
  ∷ koteckyPreissLocalSumBound
  ∷ uniformVolumeKoteckyPreissObligation
  ∷ mdlFejerDescentBookkeeping
  ∷ finiteStrongCouplingClusterExpansion
  ∷ []

data PolymerKPObligationStatus : Set where
  competitiveYMContributionTargetNotSolvedHere :
    PolymerKPObligationStatus

uniformVolumeKPObligationLabel : String
uniformVolumeKPObligationLabel =
  "prove a Kotecky-Preiss local-sum bound with constants uniform in lattice volume and compatible with cutoff/depth removal"

data PolymerKPAsMDLPromotion : Set where

polymerKPAsMDLPromotionImpossibleHere :
  PolymerKPAsMDLPromotion →
  ⊥
polymerKPAsMDLPromotionImpossibleHere ()

polymerKPAsMDLStatement : String
polymerKPAsMDLStatement =
  "The Kotecky-Preiss polymer local-sum condition is recorded as MDL/Fejer-style bookkeeping only.  The KP/uniform-volume bound is the competitive Yang-Mills contribution target and is not solved here."

record PolymerKPAsMDLReceipt : Setω where
  field
    status :
      PolymerKPAsMDLStatus

    statusIsCanonical :
      status ≡ polymerKPShapeRecordedViaMDLFejerOnly

    mdlFejerReceipt :
      Fejer.MDLFejerAxiomsShift

    finiteStrongCouplingReceipt :
      Strong.StrongCouplingExpansionReceipt

    uniformStrongCouplingReceipt :
      Uniform.UniformBoundStrongCouplingReceipt

    uniformVolumeObligationStatus :
      PolymerKPObligationStatus

    uniformVolumeObligationStatusIsTarget :
      uniformVolumeObligationStatus
      ≡
      competitiveYMContributionTargetNotSolvedHere

    uniformVolumeKPObligation :
      String

    uniformVolumeKPObligationIsCanonical :
      uniformVolumeKPObligation ≡ uniformVolumeKPObligationLabel

    surfaces :
      List PolymerKPAsMDLSurface

    surfacesAreCanonical :
      surfaces ≡ canonicalPolymerKPAsMDLSurfaces

    polymerAsDescriptionLengthRecorded :
      Bool

    polymerAsDescriptionLengthRecordedIsTrue :
      polymerAsDescriptionLengthRecorded ≡ true

    mdLFejerBookkeepingAvailable :
      Bool

    mdLFejerBookkeepingAvailableIsTrue :
      mdLFejerBookkeepingAvailable ≡ true

    finiteClusterExpansionAvailable :
      Bool

    finiteClusterExpansionAvailableIsTrue :
      finiteClusterExpansionAvailable ≡ true

    koteckyPreissConditionProved :
      Bool

    koteckyPreissConditionProvedIsFalse :
      koteckyPreissConditionProved ≡ false

    uniformVolumeKPBoundProved :
      Bool

    uniformVolumeKPBoundProvedIsFalse :
      uniformVolumeKPBoundProved ≡ false

    competitiveYMContributionTarget :
      Bool

    competitiveYMContributionTargetIsTrue :
      competitiveYMContributionTarget ≡ true

    jointPolymerExpansionImported :
      Bool

    jointPolymerExpansionImportedIsFalse :
      jointPolymerExpansionImported ≡ false

    continuumPolymerConvergenceProved :
      Bool

    continuumPolymerConvergenceProvedIsFalse :
      continuumPolymerConvergenceProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List PolymerKPAsMDLPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ polymerKPAsMDLStatement

    receiptBoundary :
      List String

open PolymerKPAsMDLReceipt public

canonicalPolymerKPAsMDLReceipt :
  PolymerKPAsMDLReceipt
canonicalPolymerKPAsMDLReceipt =
  record
    { status =
        polymerKPShapeRecordedViaMDLFejerOnly
    ; statusIsCanonical =
        refl
    ; mdlFejerReceipt =
        Fejer.mdlFejerShift
    ; finiteStrongCouplingReceipt =
        Strong.canonicalStrongCouplingExpansionReceipt
    ; uniformStrongCouplingReceipt =
        Uniform.canonicalUniformBoundStrongCouplingReceipt
    ; uniformVolumeObligationStatus =
        competitiveYMContributionTargetNotSolvedHere
    ; uniformVolumeObligationStatusIsTarget =
        refl
    ; uniformVolumeKPObligation =
        uniformVolumeKPObligationLabel
    ; uniformVolumeKPObligationIsCanonical =
        refl
    ; surfaces =
        canonicalPolymerKPAsMDLSurfaces
    ; surfacesAreCanonical =
        refl
    ; polymerAsDescriptionLengthRecorded =
        true
    ; polymerAsDescriptionLengthRecordedIsTrue =
        refl
    ; mdLFejerBookkeepingAvailable =
        true
    ; mdLFejerBookkeepingAvailableIsTrue =
        refl
    ; finiteClusterExpansionAvailable =
        true
    ; finiteClusterExpansionAvailableIsTrue =
        refl
    ; koteckyPreissConditionProved =
        false
    ; koteckyPreissConditionProvedIsFalse =
        refl
    ; uniformVolumeKPBoundProved =
        false
    ; uniformVolumeKPBoundProvedIsFalse =
        refl
    ; competitiveYMContributionTarget =
        true
    ; competitiveYMContributionTargetIsTrue =
        refl
    ; jointPolymerExpansionImported =
        false
    ; jointPolymerExpansionImportedIsFalse =
        refl
    ; continuumPolymerConvergenceProved =
        false
    ; continuumPolymerConvergenceProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        polymerKPAsMDLStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Consumes MDLFejerAxiomsShift.mdlFejerShift for descent bookkeeping"
        ∷ "Consumes finite strong-coupling and uniform-bound receipts only"
        ∷ "Does not prove the Kotecky-Preiss condition for continuum Yang-Mills"
        ∷ "The KP/uniform-volume obligation is the competitive YM contribution target: constants must be uniform in lattice volume and stable under cutoff/depth removal"
        ∷ "The KP/uniform-volume obligation is not solved or imported here"
        ∷ "Does not import any external polymer expansion proof"
        ∷ "Keeps all Clay Yang-Mills promotion flags false"
        ∷ []
    }

polymerKPAsMDLKeepsClayFalse :
  clayYangMillsPromoted canonicalPolymerKPAsMDLReceipt ≡ false
polymerKPAsMDLKeepsClayFalse =
  refl
