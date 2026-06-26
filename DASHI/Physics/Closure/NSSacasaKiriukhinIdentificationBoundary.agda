module DASHI.Physics.Closure.NSSacasaKiriukhinIdentificationBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- NSSacasaKiriukhin identification boundary receipt.
--
-- This module is a fail-closed boundary receipt for the open Sacasa -> Kiriukhin
-- bridge.  It records the candidate bridge only as a boundary object: V_N is
-- bounded by a cosphere coherence functional C_N, the intended route asks for
-- time-integrability of sup_N C_N, and the obvious shortcuts remain rejected.
-- No identification proof, no bridge promotion, and no terminal claim is made.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSSacasaKiriukhinBoundaryRow : Set where
  rowOpenSacasaToKiriukhinBridgeRecorded :
    NSSacasaKiriukhinBoundaryRow
  rowVNBoundedByCosphereCoherenceFunctionalRecorded :
    NSSacasaKiriukhinBoundaryRow
  rowTimeIntegrabilityOfSupCNRecorded :
    NSSacasaKiriukhinBoundaryRow
  rowHsGreaterThan2OnlyShortcutRejected :
    NSSacasaKiriukhinBoundaryRow
  rowEnsembleOnlyShortcutRejected :
    NSSacasaKiriukhinBoundaryRow
  rowModelOnlyShortcutRejected :
    NSSacasaKiriukhinBoundaryRow
  rowFalsePromotionGuardsRecorded :
    NSSacasaKiriukhinBoundaryRow

canonicalNSSacasaKiriukhinBoundaryRows :
  List NSSacasaKiriukhinBoundaryRow
canonicalNSSacasaKiriukhinBoundaryRows =
  rowOpenSacasaToKiriukhinBridgeRecorded
  ∷ rowVNBoundedByCosphereCoherenceFunctionalRecorded
  ∷ rowTimeIntegrabilityOfSupCNRecorded
  ∷ rowHsGreaterThan2OnlyShortcutRejected
  ∷ rowEnsembleOnlyShortcutRejected
  ∷ rowModelOnlyShortcutRejected
  ∷ rowFalsePromotionGuardsRecorded
  ∷ []

data NSSacasaKiriukhinBoundaryClaim : Set where
  claimVNBoundedByCN :
    NSSacasaKiriukhinBoundaryClaim
  claimCNIsCosphereCoherenceFunctional :
    NSSacasaKiriukhinBoundaryClaim
  claimSupCNTimeIntegrabilityDesired :
    NSSacasaKiriukhinBoundaryClaim
  claimHsGreaterThan2OnlyInsufficient :
    NSSacasaKiriukhinBoundaryClaim
  claimEnsembleOnlyInsufficient :
    NSSacasaKiriukhinBoundaryClaim
  claimModelOnlyInsufficient :
    NSSacasaKiriukhinBoundaryClaim
  claimBridgeIdentificationRemainsOpen :
    NSSacasaKiriukhinBoundaryClaim

canonicalNSSacasaKiriukhinBoundaryClaims :
  List NSSacasaKiriukhinBoundaryClaim
canonicalNSSacasaKiriukhinBoundaryClaims =
  claimVNBoundedByCN
  ∷ claimCNIsCosphereCoherenceFunctional
  ∷ claimSupCNTimeIntegrabilityDesired
  ∷ claimHsGreaterThan2OnlyInsufficient
  ∷ claimEnsembleOnlyInsufficient
  ∷ claimModelOnlyInsufficient
  ∷ claimBridgeIdentificationRemainsOpen
  ∷ []

data NSSacasaKiriukhinShortcutRejection : Set where
  hsGreaterThan2OnlyShortcut :
    NSSacasaKiriukhinShortcutRejection
  ensembleOnlyShortcut :
    NSSacasaKiriukhinShortcutRejection
  modelOnlyShortcut :
    NSSacasaKiriukhinShortcutRejection
  mixedShortcutWithoutBridgeProof :
    NSSacasaKiriukhinShortcutRejection

canonicalNSSacasaKiriukhinShortcutRejections :
  List NSSacasaKiriukhinShortcutRejection
canonicalNSSacasaKiriukhinShortcutRejections =
  hsGreaterThan2OnlyShortcut
  ∷ ensembleOnlyShortcut
  ∷ modelOnlyShortcut
  ∷ mixedShortcutWithoutBridgeProof
  ∷ []

data NSSacasaKiriukhinPromotionFlag : Set where
  promotionSacasaToKiriukhinIdentification :
    NSSacasaKiriukhinPromotionFlag
  promotionBridgePromoted :
    NSSacasaKiriukhinPromotionFlag
  promotionClayPromoted :
    NSSacasaKiriukhinPromotionFlag

canonicalNSSacasaKiriukhinPromotionFlags :
  List NSSacasaKiriukhinPromotionFlag
canonicalNSSacasaKiriukhinPromotionFlags = []

data NSSacasaKiriukhinBoundaryGate : Set where
  vNBoundedByCNGate :
    NSSacasaKiriukhinBoundaryGate
  supCNTimeIntegrabilityGate :
    NSSacasaKiriukhinBoundaryGate
  hsGreaterThan2OnlyGateClosed :
    NSSacasaKiriukhinBoundaryGate
  ensembleOnlyGateClosed :
    NSSacasaKiriukhinBoundaryGate
  modelOnlyGateClosed :
    NSSacasaKiriukhinBoundaryGate
  falsePromotionGate :
    NSSacasaKiriukhinBoundaryGate

canonicalNSSacasaKiriukhinBoundaryGates :
  List NSSacasaKiriukhinBoundaryGate
canonicalNSSacasaKiriukhinBoundaryGates =
  vNBoundedByCNGate
  ∷ supCNTimeIntegrabilityGate
  ∷ hsGreaterThan2OnlyGateClosed
  ∷ ensembleOnlyGateClosed
  ∷ modelOnlyGateClosed
  ∷ falsePromotionGate
  ∷ []

canonicalNSSacasaKiriukhinReceiptBoundary :
  List String
canonicalNSSacasaKiriukhinReceiptBoundary =
  "open Sacasa->Kiriukhin bridge is recorded as an open boundary"
  ∷ "V_N is bounded by a cosphere coherence functional C_N"
  ∷ "time-integrability of sup_N C_N is the desired route condition"
  ∷ "H^s(s>2)-only shortcut is rejected"
  ∷ "ensemble-only shortcut is rejected"
  ∷ "model-only shortcut is rejected"
  ∷ "false promotion gates remain closed"
  ∷ "no identification proof is claimed here"
  ∷ []

data NSSacasaKiriukhinBoundaryPromotion : Set where

nsSacasaKiriukhinBoundaryPromotionImpossibleHere :
  NSSacasaKiriukhinBoundaryPromotion →
  ⊥
nsSacasaKiriukhinBoundaryPromotionImpossibleHere ()

nssSacasaKiriukhinBoundaryStatement : String
nssSacasaKiriukhinBoundaryStatement =
  "Fail-closed Sacasa->Kiriukhin boundary receipt: V_N is recorded as bounded by a cosphere coherence functional C_N, the desired route asks for time-integrability of sup_N C_N, and the H^s(s>2)-only, ensemble-only, and model-only shortcuts remain rejected. No identification proof or bridge promotion is claimed."

record NSSacasaKiriukhinIdentificationBoundaryReceipt : Setω where
  field
    boundaryRows :
      List NSSacasaKiriukhinBoundaryRow
    boundaryRowsAreCanonical :
      boundaryRows ≡ canonicalNSSacasaKiriukhinBoundaryRows

    boundaryRowCount :
      Nat
    boundaryRowCountIsSeven :
      boundaryRowCount ≡ suc (suc (suc (suc (suc (suc (suc zero))))))

    boundaryClaims :
      List NSSacasaKiriukhinBoundaryClaim
    boundaryClaimsAreCanonical :
      boundaryClaims ≡ canonicalNSSacasaKiriukhinBoundaryClaims

    shortcutRejections :
      List NSSacasaKiriukhinShortcutRejection
    shortcutRejectionsAreCanonical :
      shortcutRejections ≡ canonicalNSSacasaKiriukhinShortcutRejections

    promotionFlags :
      List NSSacasaKiriukhinPromotionFlag
    promotionFlagsAreEmpty :
      promotionFlags ≡ canonicalNSSacasaKiriukhinPromotionFlags

    boundaryGates :
      List NSSacasaKiriukhinBoundaryGate
    boundaryGatesAreCanonical :
      boundaryGates ≡ canonicalNSSacasaKiriukhinBoundaryGates

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalNSSacasaKiriukhinReceiptBoundary

    openSacasaToKiriukhinBridge :
      Bool
    openSacasaToKiriukhinBridgeIsTrue :
      openSacasaToKiriukhinBridge ≡ true

    vNBoundedByCosphereCoherenceFunctional :
      Bool
    vNBoundedByCosphereCoherenceFunctionalIsTrue :
      vNBoundedByCosphereCoherenceFunctional ≡ true

    cNIsCosphereCoherenceFunctional :
      Bool
    cNIsCosphereCoherenceFunctionalIsTrue :
      cNIsCosphereCoherenceFunctional ≡ true

    supCNTimeIntegrabilityDesired :
      Bool
    supCNTimeIntegrabilityDesiredIsTrue :
      supCNTimeIntegrabilityDesired ≡ true

    hsGreaterThan2OnlyShortcutRejected :
      Bool
    hsGreaterThan2OnlyShortcutRejectedIsTrue :
      hsGreaterThan2OnlyShortcutRejected ≡ true

    ensembleOnlyShortcutRejected :
      Bool
    ensembleOnlyShortcutRejectedIsTrue :
      ensembleOnlyShortcutRejected ≡ true

    modelOnlyShortcutRejected :
      Bool
    modelOnlyShortcutRejectedIsTrue :
      modelOnlyShortcutRejected ≡ true

    identificationPromoted :
      Bool
    identificationPromotedIsFalse :
      identificationPromoted ≡ false

    bridgePromotionPromoted :
      Bool
    bridgePromotionPromotedIsFalse :
      bridgePromotionPromoted ≡ false

    clayPromotionPromoted :
      Bool
    clayPromotionPromotedIsFalse :
      clayPromotionPromoted ≡ false

    statement :
      String
    statementIsCanonical :
      statement ≡ nssSacasaKiriukhinBoundaryStatement

open NSSacasaKiriukhinIdentificationBoundaryReceipt public

canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt :
  NSSacasaKiriukhinIdentificationBoundaryReceipt
canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt =
  record
    { boundaryRows =
        canonicalNSSacasaKiriukhinBoundaryRows
    ; boundaryRowsAreCanonical =
        refl
    ; boundaryRowCount =
        suc (suc (suc (suc (suc (suc (suc zero))))))
    ; boundaryRowCountIsSeven =
        refl
    ; boundaryClaims =
        canonicalNSSacasaKiriukhinBoundaryClaims
    ; boundaryClaimsAreCanonical =
        refl
    ; shortcutRejections =
        canonicalNSSacasaKiriukhinShortcutRejections
    ; shortcutRejectionsAreCanonical =
        refl
    ; promotionFlags =
        canonicalNSSacasaKiriukhinPromotionFlags
    ; promotionFlagsAreEmpty =
        refl
    ; boundaryGates =
        canonicalNSSacasaKiriukhinBoundaryGates
    ; boundaryGatesAreCanonical =
        refl
    ; receiptBoundary =
        canonicalNSSacasaKiriukhinReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    ; openSacasaToKiriukhinBridge =
        true
    ; openSacasaToKiriukhinBridgeIsTrue =
        refl
    ; vNBoundedByCosphereCoherenceFunctional =
        true
    ; vNBoundedByCosphereCoherenceFunctionalIsTrue =
        refl
    ; cNIsCosphereCoherenceFunctional =
        true
    ; cNIsCosphereCoherenceFunctionalIsTrue =
        refl
    ; supCNTimeIntegrabilityDesired =
        true
    ; supCNTimeIntegrabilityDesiredIsTrue =
        refl
    ; hsGreaterThan2OnlyShortcutRejected =
        true
    ; hsGreaterThan2OnlyShortcutRejectedIsTrue =
        refl
    ; ensembleOnlyShortcutRejected =
        true
    ; ensembleOnlyShortcutRejectedIsTrue =
        refl
    ; modelOnlyShortcutRejected =
        true
    ; modelOnlyShortcutRejectedIsTrue =
        refl
    ; identificationPromoted =
        false
    ; identificationPromotedIsFalse =
        refl
    ; bridgePromotionPromoted =
        false
    ; bridgePromotionPromotedIsFalse =
        refl
    ; clayPromotionPromoted =
        false
    ; clayPromotionPromotedIsFalse =
        refl
    ; statement =
        nssSacasaKiriukhinBoundaryStatement
    ; statementIsCanonical =
        refl
    }

canonicalBoundaryRowCountIsSeven :
  boundaryRowCount canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ suc (suc (suc (suc (suc (suc (suc zero))))))
canonicalBoundaryRowCountIsSeven =
  refl

canonicalOpenBridgeIsTrue :
  openSacasaToKiriukhinBridge
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ true
canonicalOpenBridgeIsTrue =
  refl

canonicalVNCosphereBoundIsTrue :
  vNBoundedByCosphereCoherenceFunctional
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ true
canonicalVNCosphereBoundIsTrue =
  refl

canonicalSupCNTimeIntegrabilityIsTrue :
  supCNTimeIntegrabilityDesired
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ true
canonicalSupCNTimeIntegrabilityIsTrue =
  refl

canonicalHSGreaterThan2OnlyShortcutRejectedIsTrue :
  hsGreaterThan2OnlyShortcutRejected
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ true
canonicalHSGreaterThan2OnlyShortcutRejectedIsTrue =
  refl

canonicalEnsembleOnlyShortcutRejectedIsTrue :
  ensembleOnlyShortcutRejected
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ true
canonicalEnsembleOnlyShortcutRejectedIsTrue =
  refl

canonicalModelOnlyShortcutRejectedIsTrue :
  modelOnlyShortcutRejected
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ true
canonicalModelOnlyShortcutRejectedIsTrue =
  refl

canonicalIdentificationPromotedIsFalse :
  identificationPromoted
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ false
canonicalIdentificationPromotedIsFalse =
  refl

canonicalBridgePromotionPromotedIsFalse :
  bridgePromotionPromoted
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ false
canonicalBridgePromotionPromotedIsFalse =
  refl

canonicalClayPromotionPromotedIsFalse :
  clayPromotionPromoted
    canonicalNSSacasaKiriukhinIdentificationBoundaryReceipt
  ≡ false
canonicalClayPromotionPromotedIsFalse =
  refl
