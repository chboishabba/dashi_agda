module DASHI.Physics.Closure.NSShahmurovTwoPaperClaimIntakeReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Shahmurov two-paper claim intake receipt.
--
-- This is a checked, fail-closed intake surface for the two-paper lane.
-- It records the two arXiv identifiers, the external-review status, the
-- main checkpoints, and explicit non-promotion flags.  No postulates and no
-- imports beyond Agda.Builtin.* are used here.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSShahmurovTwoPaperClaimIntakeStatus : Set where
  intakeRecorded :
    NSShahmurovTwoPaperClaimIntakeStatus

data NSShahmurovTwoPaperClaimIntakeStage : Set where
  arxiv260501875Recorded :
    NSShahmurovTwoPaperClaimIntakeStage
  arxiv260501873Recorded :
    NSShahmurovTwoPaperClaimIntakeStage
  externalStatusUnverifiedRecorded :
    NSShahmurovTwoPaperClaimIntakeStage
  externalStatusPeerReviewPendingRecorded :
    NSShahmurovTwoPaperClaimIntakeStage
  partIAxisymmetricSwirlRecorded :
    NSShahmurovTwoPaperClaimIntakeStage
  partIIFullSystemFrontEndRecorded :
    NSShahmurovTwoPaperClaimIntakeStage
  zeroDefectRigidityRecorded :
    NSShahmurovTwoPaperClaimIntakeStage
  pohozaevMorawetzStrictnessRecorded :
    NSShahmurovTwoPaperClaimIntakeStage
  softPairBridgeRecorded :
    NSShahmurovTwoPaperClaimIntakeStage
  clayPromotionFalseRecorded :
    NSShahmurovTwoPaperClaimIntakeStage

canonicalNSShahmurovTwoPaperClaimIntakeStages :
  List NSShahmurovTwoPaperClaimIntakeStage
canonicalNSShahmurovTwoPaperClaimIntakeStages =
  arxiv260501875Recorded
  ∷ arxiv260501873Recorded
  ∷ externalStatusUnverifiedRecorded
  ∷ externalStatusPeerReviewPendingRecorded
  ∷ partIAxisymmetricSwirlRecorded
  ∷ partIIFullSystemFrontEndRecorded
  ∷ zeroDefectRigidityRecorded
  ∷ pohozaevMorawetzStrictnessRecorded
  ∷ softPairBridgeRecorded
  ∷ clayPromotionFalseRecorded
  ∷ []

data NSShahmurovTwoPaperClaimIntakeBlocker : Set where
  externalStatusUnverifiedOnly :
    NSShahmurovTwoPaperClaimIntakeBlocker
  peerReviewPendingOnly :
    NSShahmurovTwoPaperClaimIntakeBlocker
  noClaimPromotion :
    NSShahmurovTwoPaperClaimIntakeBlocker
  noClayPromotion :
    NSShahmurovTwoPaperClaimIntakeBlocker

canonicalNSShahmurovTwoPaperClaimIntakeBlockers :
  List NSShahmurovTwoPaperClaimIntakeBlocker
canonicalNSShahmurovTwoPaperClaimIntakeBlockers =
  externalStatusUnverifiedOnly
  ∷ peerReviewPendingOnly
  ∷ noClaimPromotion
  ∷ noClayPromotion
  ∷ []

arxiv260501875Text : String
arxiv260501875Text = "2605.01875"

arxiv260501873Text : String
arxiv260501873Text = "2605.01873"

externalStatusText : String
externalStatusText = "unverified/peerReviewPending"

partIAxisymmetricSwirlText : String
partIAxisymmetricSwirlText =
  "Part I axisymmetric swirl is recorded as a checkpoint only."

partIIFullSystemFrontEndText : String
partIIFullSystemFrontEndText =
  "Part II full-system front-end is recorded as a checkpoint only."

zeroDefectRigidityText : String
zeroDefectRigidityText =
  "Zero-defect rigidity is recorded as a checkpoint only."

pohozaevMorawetzStrictnessText : String
pohozaevMorawetzStrictnessText =
  "Pohozaev/Morawetz strictness is recorded as a checkpoint only."

softPairBridgeText : String
softPairBridgeText =
  "Soft pair bridge is recorded as a checkpoint only."

failClosedIntakeText : String
failClosedIntakeText =
  "The intake remains fail-closed, candidate-only, and non-promoting."

record NSShahmurovTwoPaperClaimIntakeReceipt : Set where
  field
    status :
      NSShahmurovTwoPaperClaimIntakeStatus
    statusIsCanonical :
      status ≡ intakeRecorded

    arxivIdentifiers :
      List String
    arxivIdentifiersAreCanonical :
      arxivIdentifiers ≡
      arxiv260501875Text ∷ arxiv260501873Text ∷ []

    arxivCount :
      Nat
    arxivCountIsCanonical :
      arxivCount ≡
      listLength (arxiv260501875Text ∷ arxiv260501873Text ∷ [])

    externalStatus :
      String
    externalStatusIsCanonical :
      externalStatus ≡ externalStatusText

    partIAxisymmetricSwirl :
      Bool
    partIAxisymmetricSwirlIsTrue :
      partIAxisymmetricSwirl ≡ true

    partIIFullSystemFrontEnd :
      Bool
    partIIFullSystemFrontEndIsTrue :
      partIIFullSystemFrontEnd ≡ true

    zeroDefectRigidity :
      Bool
    zeroDefectRigidityIsTrue :
      zeroDefectRigidity ≡ true

    pohozaevMorawetzStrictness :
      Bool
    pohozaevMorawetzStrictnessIsTrue :
      pohozaevMorawetzStrictness ≡ true

    softPairBridge :
      Bool
    softPairBridgeIsTrue :
      softPairBridge ≡ true

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    claimPromotion :
      Bool
    claimPromotionIsFalse :
      claimPromotion ≡ false

    intakeLedger :
      List NSShahmurovTwoPaperClaimIntakeStage
    intakeLedgerIsCanonical :
      intakeLedger ≡ canonicalNSShahmurovTwoPaperClaimIntakeStages

    blockers :
      List NSShahmurovTwoPaperClaimIntakeBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSShahmurovTwoPaperClaimIntakeBlockers

    intakeSummary :
      String
    intakeSummaryIsCanonical :
      intakeSummary ≡ failClosedIntakeText

open NSShahmurovTwoPaperClaimIntakeReceipt public

canonicalNSShahmurovTwoPaperClaimIntakeReceipt :
  NSShahmurovTwoPaperClaimIntakeReceipt
canonicalNSShahmurovTwoPaperClaimIntakeReceipt =
  record
    { status =
        intakeRecorded
    ; statusIsCanonical =
        refl
    ; arxivIdentifiers =
        arxiv260501875Text ∷ arxiv260501873Text ∷ []
    ; arxivIdentifiersAreCanonical =
        refl
    ; arxivCount =
        suc (suc zero)
    ; arxivCountIsCanonical =
        refl
    ; externalStatus =
        externalStatusText
    ; externalStatusIsCanonical =
        refl
    ; partIAxisymmetricSwirl =
        true
    ; partIAxisymmetricSwirlIsTrue =
        refl
    ; partIIFullSystemFrontEnd =
        true
    ; partIIFullSystemFrontEndIsTrue =
        refl
    ; zeroDefectRigidity =
        true
    ; zeroDefectRigidityIsTrue =
        refl
    ; pohozaevMorawetzStrictness =
        true
    ; pohozaevMorawetzStrictnessIsTrue =
        refl
    ; softPairBridge =
        true
    ; softPairBridgeIsTrue =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; claimPromotion =
        false
    ; claimPromotionIsFalse =
        refl
    ; intakeLedger =
        canonicalNSShahmurovTwoPaperClaimIntakeStages
    ; intakeLedgerIsCanonical =
        refl
    ; blockers =
        canonicalNSShahmurovTwoPaperClaimIntakeBlockers
    ; blockersAreCanonical =
        refl
    ; intakeSummary =
        failClosedIntakeText
    ; intakeSummaryIsCanonical =
        refl
    }

canonicalNSShahmurovTwoPaperClaimIntakeStatus :
  NSShahmurovTwoPaperClaimIntakeStatus
canonicalNSShahmurovTwoPaperClaimIntakeStatus =
  intakeRecorded

canonicalNSShahmurovTwoPaperClaimIntakeStatusIsCanonical :
  status canonicalNSShahmurovTwoPaperClaimIntakeReceipt
  ≡ canonicalNSShahmurovTwoPaperClaimIntakeStatus
canonicalNSShahmurovTwoPaperClaimIntakeStatusIsCanonical =
  refl

canonicalNSShahmurovTwoPaperClaimIntakeClayPromotionFalse :
  clayPromotion canonicalNSShahmurovTwoPaperClaimIntakeReceipt ≡ false
canonicalNSShahmurovTwoPaperClaimIntakeClayPromotionFalse =
  refl
