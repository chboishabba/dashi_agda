module DASHI.Physics.Closure.NSClayHardWallStandardProofObligationsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only standard-language proof obligation packet for the two
-- hard walls.
--
-- This receipt is fail-closed.  It records the two remaining hard walls
-- as prose, enumerates the exact submission-side proof obligations still
-- needed for a Clay packet, and keeps both submittable and theorem
-- promotion false.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSClayHardWallStandardPacketStatus : Set where
  candidateOnlyStandardLanguagePacketRecorded :
    NSClayHardWallStandardPacketStatus

data NSClayHardWallStandardWall : Set where
  hOmegaCtrlTheoremWall :
    NSClayHardWallStandardWall
  collapseImpossibleTheoremWall :
    NSClayHardWallStandardWall

canonicalNSClayHardWallStandardWalls :
  List NSClayHardWallStandardWall
canonicalNSClayHardWallStandardWalls =
  hOmegaCtrlTheoremWall
  ∷ collapseImpossibleTheoremWall
  ∷ []

wallLabel : NSClayHardWallStandardWall → String
wallLabel hOmegaCtrlTheoremWall =
  "h_omega_ctrl theorem"
wallLabel collapseImpossibleTheoremWall =
  "collapseImpossible theorem"

canonicalNSClayHardWallStandardWallLabels :
  List String
canonicalNSClayHardWallStandardWallLabels =
  wallLabel hOmegaCtrlTheoremWall
  ∷ wallLabel collapseImpossibleTheoremWall
  ∷ []

data NSClayHardWallStandardProofObligation : Set where
  hOmegaCtrlTheorem :
    NSClayHardWallStandardProofObligation
  pressureAndCZEstimates :
    NSClayHardWallStandardProofObligation
  qTDerivativeEstimate :
    NSClayHardWallStandardProofObligation
  commutatorEstimate :
    NSClayHardWallStandardProofObligation
  gronwallEstimate :
    NSClayHardWallStandardProofObligation
  boundarySobolevLift :
    NSClayHardWallStandardProofObligation
  ratioBound :
    NSClayHardWallStandardProofObligation
  collapseImpossibleTheorem :
    NSClayHardWallStandardProofObligation
  integrationReviewTrackA :
    NSClayHardWallStandardProofObligation

canonicalNSClayHardWallStandardProofObligations :
  List NSClayHardWallStandardProofObligation
canonicalNSClayHardWallStandardProofObligations =
  hOmegaCtrlTheorem
  ∷ pressureAndCZEstimates
  ∷ qTDerivativeEstimate
  ∷ commutatorEstimate
  ∷ gronwallEstimate
  ∷ boundarySobolevLift
  ∷ ratioBound
  ∷ collapseImpossibleTheorem
  ∷ integrationReviewTrackA
  ∷ []

obligationLabel : NSClayHardWallStandardProofObligation → String
obligationLabel hOmegaCtrlTheorem =
  "prove the h_omega_ctrl theorem"
obligationLabel pressureAndCZEstimates =
  "prove the pressure and CZ estimates"
obligationLabel qTDerivativeEstimate =
  "prove the Q(t) derivative estimate"
obligationLabel commutatorEstimate =
  "prove the commutator estimate"
obligationLabel gronwallEstimate =
  "prove the Gronwall estimate"
obligationLabel boundarySobolevLift =
  "prove the boundary Sobolev lift"
obligationLabel ratioBound =
  "establish the ratio bound"
obligationLabel collapseImpossibleTheorem =
  "prove collapseImpossible"
obligationLabel integrationReviewTrackA =
  "integration / review / Track A"

canonicalNSClayHardWallStandardObligationLabels :
  List String
canonicalNSClayHardWallStandardObligationLabels =
  obligationLabel hOmegaCtrlTheorem
  ∷ obligationLabel pressureAndCZEstimates
  ∷ obligationLabel qTDerivativeEstimate
  ∷ obligationLabel commutatorEstimate
  ∷ obligationLabel gronwallEstimate
  ∷ obligationLabel boundarySobolevLift
  ∷ obligationLabel ratioBound
  ∷ obligationLabel collapseImpossibleTheorem
  ∷ obligationLabel integrationReviewTrackA
  ∷ []

canonicalNSClayHardWallStandardReceiptStatement :
  String
canonicalNSClayHardWallStandardReceiptStatement =
  "Standard-language proof obligation packet for the two hard walls: h_omega_ctrl theorem and collapseImpossible theorem remain open. The remaining Clay submission obligations are the pressure and CZ estimates, the Q(t) derivative estimate, the commutator estimate, the Gronwall estimate, the boundary Sobolev lift, the ratio bound, collapseImpossible itself, and integration / review / Track A. submittable remains false and theorem promotion remains false."

canonicalNSClayHardWallStandardReceiptBoundary :
  List String
canonicalNSClayHardWallStandardReceiptBoundary =
  "h_omega_ctrl theorem remains open"
  ∷ "pressure/CZ, Q(t), commutator, Gronwall, boundary Sobolev lift, and ratio bound remain open"
  ∷ "collapseImpossible remains open"
  ∷ "integration / review / Track A remain open"
  ∷ "submittable remains false"
  ∷ "theorem promotion remains false"
  ∷ []

record NSClayHardWallStandardProofObligationsReceipt : Setω where
  field
    status :
      NSClayHardWallStandardPacketStatus
    statusIsCanonical :
      status ≡ candidateOnlyStandardLanguagePacketRecorded

    hardWalls :
      List NSClayHardWallStandardWall
    hardWallsAreCanonical :
      hardWalls ≡ canonicalNSClayHardWallStandardWalls
    hardWallLabels :
      List String
    hardWallLabelsAreCanonical :
      hardWallLabels ≡ canonicalNSClayHardWallStandardWallLabels
    hardWallCount :
      Nat
    hardWallCountIs2 :
      hardWallCount ≡ 2

    proofObligations :
      List NSClayHardWallStandardProofObligation
    proofObligationsAreCanonical :
      proofObligations ≡ canonicalNSClayHardWallStandardProofObligations
    obligationLabels :
      List String
    obligationLabelsAreCanonical :
      obligationLabels ≡ canonicalNSClayHardWallStandardObligationLabels
    obligationCount :
      Nat
    obligationCountIs9 :
      obligationCount ≡ 9

    statement :
      String
    statementIsCanonical :
      statement ≡ canonicalNSClayHardWallStandardReceiptStatement

    submittable :
      Bool
    submittableIsFalse :
      submittable ≡ false

    theoremPromotion :
      Bool
    theoremPromotionIsFalse :
      theoremPromotion ≡ false

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalNSClayHardWallStandardReceiptBoundary

open NSClayHardWallStandardProofObligationsReceipt public

canonicalNSClayHardWallStandardProofObligationsReceipt :
  NSClayHardWallStandardProofObligationsReceipt
canonicalNSClayHardWallStandardProofObligationsReceipt =
  record
    { status =
        candidateOnlyStandardLanguagePacketRecorded
    ; statusIsCanonical =
        refl
    ; hardWalls =
        canonicalNSClayHardWallStandardWalls
    ; hardWallsAreCanonical =
        refl
    ; hardWallLabels =
        canonicalNSClayHardWallStandardWallLabels
    ; hardWallLabelsAreCanonical =
        refl
    ; hardWallCount =
        listLength canonicalNSClayHardWallStandardWalls
    ; hardWallCountIs2 =
        refl
    ; proofObligations =
        canonicalNSClayHardWallStandardProofObligations
    ; proofObligationsAreCanonical =
        refl
    ; obligationLabels =
        canonicalNSClayHardWallStandardObligationLabels
    ; obligationLabelsAreCanonical =
        refl
    ; obligationCount =
        listLength canonicalNSClayHardWallStandardProofObligations
    ; obligationCountIs9 =
        refl
    ; statement =
        canonicalNSClayHardWallStandardReceiptStatement
    ; statementIsCanonical =
        refl
    ; submittable =
        false
    ; submittableIsFalse =
        refl
    ; theoremPromotion =
        false
    ; theoremPromotionIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; receiptBoundary =
        canonicalNSClayHardWallStandardReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

canonicalNSClayHardWallStandardStatus :
  NSClayHardWallStandardPacketStatus
canonicalNSClayHardWallStandardStatus =
  status canonicalNSClayHardWallStandardProofObligationsReceipt

canonicalNSClayHardWallStandardStatusIsCanonical :
  canonicalNSClayHardWallStandardStatus
  ≡ candidateOnlyStandardLanguagePacketRecorded
canonicalNSClayHardWallStandardStatusIsCanonical =
  refl

canonicalNSClayHardWallStandardHardWallCount :
  Nat
canonicalNSClayHardWallStandardHardWallCount =
  hardWallCount canonicalNSClayHardWallStandardProofObligationsReceipt

canonicalNSClayHardWallStandardHardWallCountIs2 :
  canonicalNSClayHardWallStandardHardWallCount ≡ 2
canonicalNSClayHardWallStandardHardWallCountIs2 =
  hardWallCountIs2 canonicalNSClayHardWallStandardProofObligationsReceipt

canonicalNSClayHardWallStandardObligationCount :
  Nat
canonicalNSClayHardWallStandardObligationCount =
  obligationCount canonicalNSClayHardWallStandardProofObligationsReceipt

canonicalNSClayHardWallStandardObligationCountIs9 :
  canonicalNSClayHardWallStandardObligationCount ≡ 9
canonicalNSClayHardWallStandardObligationCountIs9 =
  obligationCountIs9 canonicalNSClayHardWallStandardProofObligationsReceipt

canonicalNSClayHardWallStandardSubmittableIsFalse :
  submittable canonicalNSClayHardWallStandardProofObligationsReceipt ≡ false
canonicalNSClayHardWallStandardSubmittableIsFalse =
  submittableIsFalse canonicalNSClayHardWallStandardProofObligationsReceipt

canonicalNSClayHardWallStandardTheoremPromotionIsFalse :
  theoremPromotion canonicalNSClayHardWallStandardProofObligationsReceipt ≡ false
canonicalNSClayHardWallStandardTheoremPromotionIsFalse =
  theoremPromotionIsFalse canonicalNSClayHardWallStandardProofObligationsReceipt

canonicalNSClayHardWallStandardClayPromotionIsFalse :
  clayPromotion canonicalNSClayHardWallStandardProofObligationsReceipt ≡ false
canonicalNSClayHardWallStandardClayPromotionIsFalse =
  clayPromotionIsFalse canonicalNSClayHardWallStandardProofObligationsReceipt
