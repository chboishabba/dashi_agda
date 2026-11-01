module DASHI.Physics.Closure.NSBkTrajectoryMinimumReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Fail-closed B_k trajectory minimum receipt.
--
-- This module records the corrected second-variation reading for the new
-- B_k route.  At B_k = 0, the recorded expression
--   (D_t)^2 B_k = 4 |D_t Q_k|^2 >= 0
-- identifies a trajectory minimum rather than a saddle.  The generation
-- from zero remains conditional: it requires D_t Q_k != 0.
--
-- The boundary/eigenframe/pressure-Hessian language is retained only as a
-- qualitative meaning note.  No promotion is discharged here.

data NSBkTrajectoryMinimumStatus : Set where
  bkTrajectoryMinimumRecorded :
    NSBkTrajectoryMinimumStatus

data NSBkTrajectoryMinimumStage : Set where
  bkZeroTrajectoryMinimumRecorded :
    NSBkTrajectoryMinimumStage
  secondVariationNonnegativeRecorded :
    NSBkTrajectoryMinimumStage
  dtQkNonzeroRequiredForGenerationRecorded :
    NSBkTrajectoryMinimumStage
  boundaryEigenframePressureHessianMeaningRecorded :
    NSBkTrajectoryMinimumStage
  failClosedReceiptRecorded :
    NSBkTrajectoryMinimumStage

canonicalNSBkTrajectoryMinimumStages :
  List NSBkTrajectoryMinimumStage
canonicalNSBkTrajectoryMinimumStages =
  bkZeroTrajectoryMinimumRecorded
  ∷ secondVariationNonnegativeRecorded
  ∷ dtQkNonzeroRequiredForGenerationRecorded
  ∷ boundaryEigenframePressureHessianMeaningRecorded
  ∷ failClosedReceiptRecorded
  ∷ []

data NSBkTrajectoryMinimumBlocker : Set where
  saddleInterpretationRejected :
    NSBkTrajectoryMinimumBlocker
  generationFromZeroStillRequiresNonzeroDtQk :
    NSBkTrajectoryMinimumBlocker
  boundaryEigenframePressureHessianOnlyQualitative :
    NSBkTrajectoryMinimumBlocker
  theoremPromotionGateKeptClosed :
    NSBkTrajectoryMinimumBlocker
  clayPromotionGateKeptClosed :
    NSBkTrajectoryMinimumBlocker

canonicalNSBkTrajectoryMinimumBlockers :
  List NSBkTrajectoryMinimumBlocker
canonicalNSBkTrajectoryMinimumBlockers =
  saddleInterpretationRejected
  ∷ generationFromZeroStillRequiresNonzeroDtQk
  ∷ boundaryEigenframePressureHessianOnlyQualitative
  ∷ theoremPromotionGateKeptClosed
  ∷ clayPromotionGateKeptClosed
  ∷ []

data NSBkTrajectoryMinimumPromotion : Set where

nsBkTrajectoryMinimumPromotionImpossibleHere :
  NSBkTrajectoryMinimumPromotion →
  ⊥
nsBkTrajectoryMinimumPromotionImpossibleHere ()

canonicalBkZeroTrajectoryText : String
canonicalBkZeroTrajectoryText =
  "At B_k = 0, the recorded second-variation reading is (D_t)^2 B_k = 4|D_t Q_k|^2 >= 0."

canonicalSecondVariationText : String
canonicalSecondVariationText =
  "The sign is nonnegative, so the recorded critical trajectory point is a minimum rather than a saddle."

canonicalGenerationRequirementText : String
canonicalGenerationRequirementText =
  "Generation from zero is recorded as conditional: D_t Q_k != 0 is required."

canonicalBoundaryEigenframePressureHessianText : String
canonicalBoundaryEigenframePressureHessianText =
  "Boundary/eigenframe/pressure-Hessian meaning is qualitative only; the receipt records interpretation labels, not a promoted theorem."

canonicalFailClosedText : String
canonicalFailClosedText =
  "Fail-closed ledger: the minimum is recorded, the generation condition is recorded, and theorem/Clay promotion stay false."

canonicalReceiptBoundaryText : List String
canonicalReceiptBoundaryText =
  "B_k = 0 is the recorded critical trajectory point."
  ∷ "(D_t)^2 B_k = 4|D_t Q_k|^2 >= 0 is the recorded second-variation formula."
  ∷ "The critical point is a trajectory minimum, not a saddle."
  ∷ "Zero-state generation still requires D_t Q_k != 0."
  ∷ "Boundary, eigenframe, and pressure-Hessian language is qualitative only."
  ∷ "No theorem promotion and no Clay promotion are discharged here."
  ∷ []

record NSBkTrajectoryMinimumORCSLPGF : Set where
  constructor mkNSBkTrajectoryMinimumORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record the corrected B_k trajectory minimum result as a fail-closed receipt."

    R : String
    RIsCanonical : R ≡
      "R: At B_k = 0, record (D_t)^2 B_k = 4|D_t Q_k|^2 >= 0, identify a trajectory minimum rather than a saddle, and keep generation from zero conditional on D_t Q_k != 0."

    C : String
    CIsCanonical : C ≡
      "C: Keep the receipt self-contained with stage and blocker ledgers, canonical texts, and explicit promotion gates."

    S : String
    SIsCanonical : S ≡
      "S: B_k=0 recorded=true; secondVariationNonnegative=true; minimumNotSaddle=true; generationFromZeroRequiresNonzeroDtQk=true; boundaryEigenframePressureHessianMeaningQualitativeOnly=true; theoremPromotion=false; clayPromotion=false."

    L : String
    LIsCanonical : L ≡
      "L: Treat this as a local diagnostic lane for the B_k second-variation reading, not as a promoted closure theorem."

    P : String
    PIsCanonical : P ≡
      "P: No theorem is promoted from this receipt."

    G : String
    GIsCanonical : G ≡
      "G: No Clay promotion, no hidden quantitative upgrade, and no stronger geometric claim are accepted here."

    F : String
    FIsCanonical : F ≡
      "F: The route stays fail-closed because the minimum is recorded, the generation condition is conditional, and the qualitative interpretation remains unpromoted."

record NSBkTrajectoryMinimumReceipt : Setω where
  constructor mkNSBkTrajectoryMinimumReceipt
  field
    status :
      NSBkTrajectoryMinimumStatus

    statusIsCanonical :
      status ≡ bkTrajectoryMinimumRecorded

    stageTrail :
      List NSBkTrajectoryMinimumStage

    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSBkTrajectoryMinimumStages

    stageCount :
      Nat

    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSBkTrajectoryMinimumStages

    blockerTrail :
      List NSBkTrajectoryMinimumBlocker

    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSBkTrajectoryMinimumBlockers

    blockerCount :
      Nat

    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSBkTrajectoryMinimumBlockers

    bkZeroTrajectoryText :
      String

    bkZeroTrajectoryTextIsCanonical :
      bkZeroTrajectoryText ≡ canonicalBkZeroTrajectoryText

    secondVariationText :
      String

    secondVariationTextIsCanonical :
      secondVariationText ≡ canonicalSecondVariationText

    generationRequirementText :
      String

    generationRequirementTextIsCanonical :
      generationRequirementText ≡ canonicalGenerationRequirementText

    boundaryEigenframePressureHessianText :
      String

    boundaryEigenframePressureHessianTextIsCanonical :
      boundaryEigenframePressureHessianText ≡ canonicalBoundaryEigenframePressureHessianText

    failClosedText :
      String

    failClosedTextIsCanonical :
      failClosedText ≡ canonicalFailClosedText

    receiptBoundaryText :
      List String

    receiptBoundaryTextIsCanonical :
      receiptBoundaryText ≡ canonicalReceiptBoundaryText

    trajectoryMinimumRecorded :
      Bool

    trajectoryMinimumRecordedIsTrue :
      trajectoryMinimumRecorded ≡ true

    generationFromZeroRequiresNonzeroDtQk :
      Bool

    generationFromZeroRequiresNonzeroDtQkIsTrue :
      generationFromZeroRequiresNonzeroDtQk ≡ true

    saddleClaim :
      Bool

    saddleClaimIsFalse :
      saddleClaim ≡ false

    theoremPromotion :
      Bool

    theoremPromotionIsFalse :
      theoremPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    orcslpgf :
      NSBkTrajectoryMinimumORCSLPGF

open NSBkTrajectoryMinimumReceipt public

canonicalNSBkTrajectoryMinimumORCSLPGF :
  NSBkTrajectoryMinimumORCSLPGF
canonicalNSBkTrajectoryMinimumORCSLPGF =
  mkNSBkTrajectoryMinimumORCSLPGF
    "O: Record the corrected B_k trajectory minimum result as a fail-closed receipt."
    refl
    "R: At B_k = 0, record (D_t)^2 B_k = 4|D_t Q_k|^2 >= 0, identify a trajectory minimum rather than a saddle, and keep generation from zero conditional on D_t Q_k != 0."
    refl
    "C: Keep the receipt self-contained with stage and blocker ledgers, canonical texts, and explicit promotion gates."
    refl
    "S: B_k=0 recorded=true; secondVariationNonnegative=true; minimumNotSaddle=true; generationFromZeroRequiresNonzeroDtQk=true; boundaryEigenframePressureHessianMeaningQualitativeOnly=true; theoremPromotion=false; clayPromotion=false."
    refl
    "L: Treat this as a local diagnostic lane for the B_k second-variation reading, not as a promoted closure theorem."
    refl
    "P: No theorem is promoted from this receipt."
    refl
    "G: No Clay promotion, no hidden quantitative upgrade, and no stronger geometric claim are accepted here."
    refl
    "F: The route stays fail-closed because the minimum is recorded, the generation condition is conditional, and the qualitative interpretation remains unpromoted."
    refl

canonicalNSBkTrajectoryMinimumReceipt :
  NSBkTrajectoryMinimumReceipt
canonicalNSBkTrajectoryMinimumReceipt =
  record
    { status =
        bkTrajectoryMinimumRecorded
    ; statusIsCanonical =
        refl
    ; stageTrail =
        canonicalNSBkTrajectoryMinimumStages
    ; stageTrailIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSBkTrajectoryMinimumStages
    ; stageCountIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSBkTrajectoryMinimumBlockers
    ; blockerTrailIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSBkTrajectoryMinimumBlockers
    ; blockerCountIsCanonical =
        refl
    ; bkZeroTrajectoryText =
        canonicalBkZeroTrajectoryText
    ; bkZeroTrajectoryTextIsCanonical =
        refl
    ; secondVariationText =
        canonicalSecondVariationText
    ; secondVariationTextIsCanonical =
        refl
    ; generationRequirementText =
        canonicalGenerationRequirementText
    ; generationRequirementTextIsCanonical =
        refl
    ; boundaryEigenframePressureHessianText =
        canonicalBoundaryEigenframePressureHessianText
    ; boundaryEigenframePressureHessianTextIsCanonical =
        refl
    ; failClosedText =
        canonicalFailClosedText
    ; failClosedTextIsCanonical =
        refl
    ; receiptBoundaryText =
        canonicalReceiptBoundaryText
    ; receiptBoundaryTextIsCanonical =
        refl
    ; trajectoryMinimumRecorded =
        true
    ; trajectoryMinimumRecordedIsTrue =
        refl
    ; generationFromZeroRequiresNonzeroDtQk =
        true
    ; generationFromZeroRequiresNonzeroDtQkIsTrue =
        refl
    ; saddleClaim =
        false
    ; saddleClaimIsFalse =
        refl
    ; theoremPromotion =
        false
    ; theoremPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; orcslpgf =
        canonicalNSBkTrajectoryMinimumORCSLPGF
    }
