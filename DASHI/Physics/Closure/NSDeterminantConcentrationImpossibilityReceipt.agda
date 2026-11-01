module DASHI.Physics.Closure.NSDeterminantConcentrationImpossibilityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed receipt for the Case B / critical-concentration determinant
-- tranche.
--
-- This module records two separate ledger rows and keeps the lane explicitly
-- non-promoting:
--   1) Case B impossibility route via Betchov when the large-strain set stays
--      inside Omega_K.
--   2) A stronger bounded-determinant / critical-concentration impossibility
--      route recorded as a separate ledger row.
--
-- No theorem promotion, no Clay promotion, and no terminal closure are
-- discharged here.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSDeterminantConcentrationImpossibilityStatus : Set where
  determinantConcentrationImpossibilityReceiptRecorded :
    NSDeterminantConcentrationImpossibilityStatus

data NSDeterminantConcentrationImpossibilityStage : Set where
  caseBViaBetchovLargeStrainInsideOmegaKRecorded :
    NSDeterminantConcentrationImpossibilityStage
  caseBImpossibilityRecorded :
    NSDeterminantConcentrationImpossibilityStage
  boundedDeterminantCriticalConcentrationRouteRecorded :
    NSDeterminantConcentrationImpossibilityStage
  separateLedgerRowRecorded :
    NSDeterminantConcentrationImpossibilityStage
  promotionGateKeptClosedRecorded :
    NSDeterminantConcentrationImpossibilityStage
  clayGateKeptClosedRecorded :
    NSDeterminantConcentrationImpossibilityStage

canonicalNSDeterminantConcentrationImpossibilityStages :
  List NSDeterminantConcentrationImpossibilityStage
canonicalNSDeterminantConcentrationImpossibilityStages =
  caseBViaBetchovLargeStrainInsideOmegaKRecorded
  ∷ caseBImpossibilityRecorded
  ∷ boundedDeterminantCriticalConcentrationRouteRecorded
  ∷ separateLedgerRowRecorded
  ∷ promotionGateKeptClosedRecorded
  ∷ clayGateKeptClosedRecorded
  ∷ []

data NSDeterminantConcentrationImpossibilityBlocker : Set where
  caseBRequiresRecordedCarrierWitness :
    NSDeterminantConcentrationImpossibilityBlocker
  boundedDeterminantRouteIsSeparateLedgerOnly :
    NSDeterminantConcentrationImpossibilityBlocker
  theoremPromotionGateClosed :
    NSDeterminantConcentrationImpossibilityBlocker
  clayPromotionGateClosed :
    NSDeterminantConcentrationImpossibilityBlocker

canonicalNSDeterminantConcentrationImpossibilityBlockers :
  List NSDeterminantConcentrationImpossibilityBlocker
canonicalNSDeterminantConcentrationImpossibilityBlockers =
  caseBRequiresRecordedCarrierWitness
  ∷ boundedDeterminantRouteIsSeparateLedgerOnly
  ∷ theoremPromotionGateClosed
  ∷ clayPromotionGateClosed
  ∷ []

data NSDeterminantConcentrationImpossibilityPromotion : Set where

nsDeterminantConcentrationImpossibilityPromotionImpossibleHere :
  NSDeterminantConcentrationImpossibilityPromotion → ⊥
nsDeterminantConcentrationImpossibilityPromotionImpossibleHere ()

canonicalCaseBViaBetchovText : String
canonicalCaseBViaBetchovText =
  "Case B impossibility row: when the large-strain set stays inside Omega_K, the Betchov route is recorded as the obstruction witness and no closure promotion is discharged."

canonicalBoundedDeterminantText : String
canonicalBoundedDeterminantText =
  "Separate ledger row: the bounded-determinant / critical-concentration impossibility route is recorded independently and remains non-promoting."

canonicalBoundaryText : String
canonicalBoundaryText =
  "Fail-closed receipt: the Case B / critical-concentration determinant tranche is recorded as two separate impossibility rows, with theorem and Clay promotion kept false."

canonicalCaseBRouteRow : String
canonicalCaseBRouteRow =
  "Ledger row 1: Betchov obstruction for Case B under the hypothesis that the large-strain set remains inside Omega_K."

canonicalCriticalConcentrationRow : String
canonicalCriticalConcentrationRow =
  "Ledger row 2: stronger bounded-determinant / critical-concentration impossibility route recorded separately."

canonicalReceiptRows : List String
canonicalReceiptRows =
  canonicalCaseBRouteRow
  ∷ canonicalCriticalConcentrationRow
  ∷ canonicalBoundaryText
  ∷ []

canonicalOText : String
canonicalOText =
  "O: record the Case B / critical-concentration determinant tranche as a fail-closed receipt."

canonicalRText : String
canonicalRText =
  "R: record the Betchov Case B impossibility route and the separate bounded-determinant / critical-concentration route."

canonicalCText : String
canonicalCText =
  "C: the file is a ledger only; it records two impossibility rows and does not prove any promoted theorem."

canonicalSText : String
canonicalSText =
  "S: large-strain inside Omega_K -> Betchov obstruction for Case B; bounded-determinant / critical-concentration is tracked as a separate row; promotion flags remain false."

canonicalLText : String
canonicalLText =
  "L: keep the two rows separate so the bounded-determinant route does not get conflated with the Betchov Case B row."

canonicalPText : String
canonicalPText =
  "P: theorem promotion stays false."

canonicalGText : String
canonicalGText =
  "G: Clay promotion stays false."

canonicalFText : String
canonicalFText =
  "F: the receipt is explicitly non-promoting and fail-closed."

record NSDeterminantConcentrationImpossibilityReceiptORCSLPGF : Set where
  constructor mkNSDeterminantConcentrationImpossibilityReceiptORCSLPGF
  field
    O : String
    OIsCanonical :
      O ≡ canonicalOText

    R : String
    RIsCanonical :
      R ≡ canonicalRText

    C : String
    CIsCanonical :
      C ≡ canonicalCText

    S : String
    SIsCanonical :
      S ≡ canonicalSText

    L : String
    LIsCanonical :
      L ≡ canonicalLText

    P : String
    PIsCanonical :
      P ≡ canonicalPText

    G : String
    GIsCanonical :
      G ≡ canonicalGText

    F : String
    FIsCanonical :
      F ≡ canonicalFText

record NSDeterminantConcentrationImpossibilityReceipt : Setω where
  constructor mkNSDeterminantConcentrationImpossibilityReceipt
  field
    status :
      NSDeterminantConcentrationImpossibilityStatus
    statusIsCanonical :
      status ≡ determinantConcentrationImpossibilityReceiptRecorded

    stageTrail :
      List NSDeterminantConcentrationImpossibilityStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSDeterminantConcentrationImpossibilityStages
    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSDeterminantConcentrationImpossibilityStages

    blockerTrail :
      List NSDeterminantConcentrationImpossibilityBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSDeterminantConcentrationImpossibilityBlockers
    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSDeterminantConcentrationImpossibilityBlockers

    caseBViaBetchovText :
      String
    caseBViaBetchovTextIsCanonical :
      caseBViaBetchovText ≡ canonicalCaseBViaBetchovText

    boundedDeterminantText :
      String
    boundedDeterminantTextIsCanonical :
      boundedDeterminantText ≡ canonicalBoundedDeterminantText

    receiptRows :
      List String
    receiptRowsIsCanonical :
      receiptRows ≡ canonicalReceiptRows

    theoremPromotionFlag :
      Bool
    theoremPromotionFlagIsFalse :
      theoremPromotionFlag ≡ false

    clayPromotionFlag :
      Bool
    clayPromotionFlagIsFalse :
      clayPromotionFlag ≡ false

    promotionGateClosed :
      Bool
    promotionGateClosedIsTrue :
      promotionGateClosed ≡ true

    orcslpgf :
      NSDeterminantConcentrationImpossibilityReceiptORCSLPGF

canonicalNSDeterminantConcentrationImpossibilityORCSLPGF :
  NSDeterminantConcentrationImpossibilityReceiptORCSLPGF
canonicalNSDeterminantConcentrationImpossibilityORCSLPGF =
  mkNSDeterminantConcentrationImpossibilityReceiptORCSLPGF
    canonicalOText
    refl
    canonicalRText
    refl
    canonicalCText
    refl
    canonicalSText
    refl
    canonicalLText
    refl
    canonicalPText
    refl
    canonicalGText
    refl
    canonicalFText
    refl

canonicalNSDeterminantConcentrationImpossibilityReceipt :
  NSDeterminantConcentrationImpossibilityReceipt
canonicalNSDeterminantConcentrationImpossibilityReceipt =
  mkNSDeterminantConcentrationImpossibilityReceipt
    determinantConcentrationImpossibilityReceiptRecorded
    refl
    canonicalNSDeterminantConcentrationImpossibilityStages
    refl
    (listLength canonicalNSDeterminantConcentrationImpossibilityStages)
    refl
    canonicalNSDeterminantConcentrationImpossibilityBlockers
    refl
    (listLength canonicalNSDeterminantConcentrationImpossibilityBlockers)
    refl
    canonicalCaseBViaBetchovText
    refl
    canonicalBoundedDeterminantText
    refl
    canonicalReceiptRows
    refl
    false
    refl
    false
    refl
    true
    refl
    canonicalNSDeterminantConcentrationImpossibilityORCSLPGF

open NSDeterminantConcentrationImpossibilityReceipt public
