module DASHI.Physics.Closure.NSVorticityStretchingExactReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Fail-closed receipt for the exact vorticity-stretching identity.
--
-- The receipt records the exact transport law
--
--   Dt omega = S·omega
--
-- together with the exact antisymmetric cancellation
--
--   Omega_ant·omega = 1/2 (omega x omega) = 0
--
-- so the antisymmetric contribution drops identically.  The module is
-- ledger-only: no theorem promotion is claimed, no Clay promotion is
-- claimed, and the receipt boundary stays explicitly non-promoting.

data NSVorticityStretchingExactStatus : Set where
  exactDtOmegaAndAntisymmetricCancellationRecorded :
    NSVorticityStretchingExactStatus

data NSVorticityStretchingExactRow : Set where
  dtOmegaEqualsSOmegaRecorded :
    NSVorticityStretchingExactRow
  omegaStretchingTermRecorded :
    NSVorticityStretchingExactRow
  omegaAntDotOmegaCancellationRecorded :
    NSVorticityStretchingExactRow
  antisymmetricTermDropsIdenticallyRecorded :
    NSVorticityStretchingExactRow
  noTheoremPromotionRecorded :
    NSVorticityStretchingExactRow
  noClayPromotionRecorded :
    NSVorticityStretchingExactRow
  failClosedBoundaryRecorded :
    NSVorticityStretchingExactRow

canonicalNSVorticityStretchingExactRows :
  List NSVorticityStretchingExactRow
canonicalNSVorticityStretchingExactRows =
  dtOmegaEqualsSOmegaRecorded
  ∷ omegaStretchingTermRecorded
  ∷ omegaAntDotOmegaCancellationRecorded
  ∷ antisymmetricTermDropsIdenticallyRecorded
  ∷ noTheoremPromotionRecorded
  ∷ noClayPromotionRecorded
  ∷ failClosedBoundaryRecorded
  ∷ []

data NSVorticityStretchingExactBlocker : Set where
  noIndependentTheoremPromotion :
    NSVorticityStretchingExactBlocker
  noClayPromotionGate :
    NSVorticityStretchingExactBlocker
  antisymmetricTermAlreadyZero :
    NSVorticityStretchingExactBlocker
  exactCarrierProofNotExpanded :
    NSVorticityStretchingExactBlocker

canonicalNSVorticityStretchingExactBlockers :
  List NSVorticityStretchingExactBlocker
canonicalNSVorticityStretchingExactBlockers =
  noIndependentTheoremPromotion
  ∷ noClayPromotionGate
  ∷ antisymmetricTermAlreadyZero
  ∷ exactCarrierProofNotExpanded
  ∷ []

data NSVorticityStretchingExactPromotion : Set where

nsVorticityStretchingExactPromotionImpossibleHere :
  NSVorticityStretchingExactPromotion →
  ⊥
nsVorticityStretchingExactPromotionImpossibleHere ()

exactDtOmegaText : String
exactDtOmegaText = "Dt omega = S·omega"

exactOmegaAntCancellationText : String
exactOmegaAntCancellationText =
  "Omega_ant·omega = 1/2 (omega x omega) = 0"

antisymmetricDropText : String
antisymmetricDropText =
  "The antisymmetric term drops identically: Omega_ant·omega vanishes pointwise, so the stretching identity reduces exactly to the symmetric strain contribution."

noTheoremPromotionText : String
noTheoremPromotionText =
  "No theorem promotion is claimed from this receipt."

noClayPromotionText : String
noClayPromotionText =
  "No Clay promotion is claimed from this receipt."

receiptBoundaryText : List String
receiptBoundaryText =
  "Exact identity recorded: Dt omega = S·omega"
  ∷ "Exact cancellation recorded: Omega_ant·omega = 1/2 (omega x omega) = 0"
  ∷ "The antisymmetric term drops identically"
  ∷ "The receipt is fail-closed and non-promoting"
  ∷ "No theorem promotion is claimed"
  ∷ "No Clay promotion is claimed"
  ∷ []

record NSVorticityStretchingExactReceipt : Setω where
  field
    status :
      NSVorticityStretchingExactStatus

    statusIsCanonical :
      status ≡ exactDtOmegaAndAntisymmetricCancellationRecorded

    rowLedger :
      List NSVorticityStretchingExactRow

    rowLedgerIsCanonical :
      rowLedger ≡ canonicalNSVorticityStretchingExactRows

    blockerLedger :
      List NSVorticityStretchingExactBlocker

    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalNSVorticityStretchingExactBlockers

    exactDtOmega :
      String

    exactDtOmegaIsCanonical :
      exactDtOmega ≡ exactDtOmegaText

    exactOmegaAntCancellation :
      String

    exactOmegaAntCancellationIsCanonical :
      exactOmegaAntCancellation ≡ exactOmegaAntCancellationText

    antisymmetricDrop :
      String

    antisymmetricDropIsCanonical :
      antisymmetricDrop ≡ antisymmetricDropText

    noTheoremPromotion :
      Bool

    noTheoremPromotionIsFalse :
      noTheoremPromotion ≡ false

    noClayPromotion :
      Bool

    noClayPromotionIsFalse :
      noClayPromotion ≡ false

    noTheoremPromotionTextField :
      String

    noTheoremPromotionTextFieldIsCanonical :
      noTheoremPromotionTextField ≡ noTheoremPromotionText

    noClayPromotionTextField :
      String

    noClayPromotionTextFieldIsCanonical :
      noClayPromotionTextField ≡ noClayPromotionText

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

open NSVorticityStretchingExactReceipt public

canonicalNSVorticityStretchingExactReceipt :
  NSVorticityStretchingExactReceipt
canonicalNSVorticityStretchingExactReceipt =
  record
    { status =
        exactDtOmegaAndAntisymmetricCancellationRecorded
    ; statusIsCanonical =
        refl
    ; rowLedger =
        canonicalNSVorticityStretchingExactRows
    ; rowLedgerIsCanonical =
        refl
    ; blockerLedger =
        canonicalNSVorticityStretchingExactBlockers
    ; blockerLedgerIsCanonical =
        refl
    ; exactDtOmega =
        exactDtOmegaText
    ; exactDtOmegaIsCanonical =
        refl
    ; exactOmegaAntCancellation =
        exactOmegaAntCancellationText
    ; exactOmegaAntCancellationIsCanonical =
        refl
    ; antisymmetricDrop =
        antisymmetricDropText
    ; antisymmetricDropIsCanonical =
        refl
    ; noTheoremPromotion =
        false
    ; noTheoremPromotionIsFalse =
        refl
    ; noClayPromotion =
        false
    ; noClayPromotionIsFalse =
        refl
    ; noTheoremPromotionTextField =
        noTheoremPromotionText
    ; noTheoremPromotionTextFieldIsCanonical =
        refl
    ; noClayPromotionTextField =
        noClayPromotionText
    ; noClayPromotionTextFieldIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

exactDtOmegaStaysCanonical :
  exactDtOmega canonicalNSVorticityStretchingExactReceipt ≡ exactDtOmegaText
exactDtOmegaStaysCanonical =
  refl

exactOmegaAntCancellationStaysCanonical :
  exactOmegaAntCancellation canonicalNSVorticityStretchingExactReceipt ≡
  exactOmegaAntCancellationText
exactOmegaAntCancellationStaysCanonical =
  refl

antisymmetricDropStaysCanonical :
  antisymmetricDrop canonicalNSVorticityStretchingExactReceipt ≡
  antisymmetricDropText
antisymmetricDropStaysCanonical =
  refl

theoremPromotionStaysFalse :
  noTheoremPromotion canonicalNSVorticityStretchingExactReceipt ≡ false
theoremPromotionStaysFalse =
  refl

clayPromotionStaysFalse :
  noClayPromotion canonicalNSVorticityStretchingExactReceipt ≡ false
clayPromotionStaysFalse =
  refl
