module DASHI.Physics.Closure.NSTriadSignedLaplacianIdentityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- NS triad signed-operator identity receipt.
--
-- Candidate surface only:
--   on im(L_abs), L_signed_norm = I - 2 K_N
--
-- This module records the signed-operator identity as an audited receipt,
-- not as a promoted theorem.  The naming cleanup uses L_abs, L_neg, and
-- L_signed.  The exact endpoint confusion between lower and upper spectral
-- edges is explicitly guarded against.  All promotion flags remain false.

data NSTriadSignedLaplacianIdentityStatus : Set where
  candidateSignedOperatorIdentityRecorded :
    NSTriadSignedLaplacianIdentityStatus

data NSTriadSignedLaplacianIdentityAssumption : Set where
  lAbsNamingCleanup :
    NSTriadSignedLaplacianIdentityAssumption
  lNegNamingCleanup :
    NSTriadSignedLaplacianIdentityAssumption
  lSignedNamingCleanup :
    NSTriadSignedLaplacianIdentityAssumption
  positiveSubspaceRestriction :
    NSTriadSignedLaplacianIdentityAssumption
  exactIdentityOnImLAbs :
    NSTriadSignedLaplacianIdentityAssumption
  nonPromotingAuditMode :
    NSTriadSignedLaplacianIdentityAssumption

canonicalNSTriadSignedLaplacianIdentityAssumptions :
  List NSTriadSignedLaplacianIdentityAssumption
canonicalNSTriadSignedLaplacianIdentityAssumptions =
  lAbsNamingCleanup
  ∷ lNegNamingCleanup
  ∷ lSignedNamingCleanup
  ∷ positiveSubspaceRestriction
  ∷ exactIdentityOnImLAbs
  ∷ nonPromotingAuditMode
  ∷ []

candidateSignedOperatorIdentityText : String
candidateSignedOperatorIdentityText =
  "candidate identity surface recorded on im(L_abs): L_signed_norm = I - 2 K_N"

endpointConfusionGuardText : String
endpointConfusionGuardText =
  "exact endpoint confusion is guarded against: the lower spectral edge is not the upper spectral edge, the audited labels are L_abs, L_neg, and L_signed, and the positive-subspace restriction must not be swapped"

auditModeText : String
auditModeText =
  "audit mode only: the identity surface is recorded as a receipt, not promoted as a theorem"

data NSTriadSignedLaplacianIdentityBlocker : Set where
  noTheoremPromotion :
    NSTriadSignedLaplacianIdentityBlocker
  noFullNSPromotion :
    NSTriadSignedLaplacianIdentityBlocker
  noClayPromotion :
    NSTriadSignedLaplacianIdentityBlocker
  noEndpointConfusion :
    NSTriadSignedLaplacianIdentityBlocker

canonicalNSTriadSignedLaplacianIdentityBlockers :
  List NSTriadSignedLaplacianIdentityBlocker
canonicalNSTriadSignedLaplacianIdentityBlockers =
  noTheoremPromotion
  ∷ noFullNSPromotion
  ∷ noClayPromotion
  ∷ noEndpointConfusion
  ∷ []

record NSTriadSignedLaplacianIdentityReceiptORCSLPGF : Set where
  constructor mkNSTriadSignedLaplacianIdentityReceiptORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: record the active NS triad signed-operator receipt boundary."

    R : String
    RIsCanonical : R ≡
      "R: record the naming cleanup L_abs, L_neg, and L_signed, and record the positive-subspace identity on im(L_abs) as an audited candidate receipt."

    C : String
    CIsCanonical : C ≡
      "C: this is a fail-closed receipt module, not a theorem carrier."

    S : String
    SIsCanonical : S ≡
      "S: the identity surface is candidate-only; the positive-subspace restriction is explicit; endpoint confusion is blocked; promotion flags remain false."

    L : String
    LIsCanonical : L ≡
      "L: L_abs -> L_neg -> L_signed -> im(L_abs) exact identity -> audited receipt -> no theorem promotion."

    P : String
    PIsCanonical : P ≡
      "P: keep the positive-subspace identity on im(L_abs) as an audit boundary, not a promoted proof."

    G : String
    GIsCanonical : G ≡
      "G: theorem, full NS, and Clay promotion remain false."

    F : String
    FIsCanonical : F ≡
      "F: the exact positive-subspace identity is guarded; lower/upper edge confusion is excluded from the receipt."

canonicalNSTriadSignedLaplacianIdentityReceiptORCSLPGF :
  NSTriadSignedLaplacianIdentityReceiptORCSLPGF
canonicalNSTriadSignedLaplacianIdentityReceiptORCSLPGF =
  mkNSTriadSignedLaplacianIdentityReceiptORCSLPGF
    "O: record the active NS triad signed-operator receipt boundary."
    refl
    "R: record the naming cleanup L_abs, L_neg, and L_signed, and record the positive-subspace identity on im(L_abs) as an audited candidate receipt."
    refl
    "C: this is a fail-closed receipt module, not a theorem carrier."
    refl
    "S: the identity surface is candidate-only; the positive-subspace restriction is explicit; endpoint confusion is blocked; promotion flags remain false."
    refl
    "L: L_abs -> L_neg -> L_signed -> im(L_abs) exact identity -> audited receipt -> no theorem promotion."
    refl
    "P: keep the positive-subspace identity on im(L_abs) as an audit boundary, not a promoted proof."
    refl
    "G: theorem, full NS, and Clay promotion remain false."
    refl
    "F: the exact positive-subspace identity is guarded; lower/upper edge confusion is excluded from the receipt."
    refl

record NSTriadSignedLaplacianIdentityReceipt : Setω where
  constructor mkNSTriadSignedLaplacianIdentityReceipt
  field
    status :
      NSTriadSignedLaplacianIdentityStatus

    statusIsCanonical :
      status ≡ candidateSignedOperatorIdentityRecorded

    assumptionLedger :
      List NSTriadSignedLaplacianIdentityAssumption

    assumptionLedgerIsCanonical :
      assumptionLedger ≡ canonicalNSTriadSignedLaplacianIdentityAssumptions

    assumptionCount :
      Nat

    assumptionCountIsCanonical :
      assumptionCount ≡ listLength canonicalNSTriadSignedLaplacianIdentityAssumptions

    blockerLedger :
      List NSTriadSignedLaplacianIdentityBlocker

    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalNSTriadSignedLaplacianIdentityBlockers

    blockerCount :
      Nat

    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSTriadSignedLaplacianIdentityBlockers

    signedOperatorIdentitySurfaceTextField :
      String

    signedOperatorIdentitySurfaceTextFieldIsCanonical :
      signedOperatorIdentitySurfaceTextField ≡ candidateSignedOperatorIdentityText

    endpointConfusionGuardTextField :
      String

    endpointConfusionGuardTextFieldIsCanonical :
      endpointConfusionGuardTextField ≡ endpointConfusionGuardText

    auditMode :
      String

    auditModeIsCanonical :
      auditMode ≡ auditModeText

    positiveSubspaceRestricted :
      Bool

    positiveSubspaceRestrictedIsTrue :
      positiveSubspaceRestricted ≡ true

    exactIdentityOnImLAbsRecorded :
      Bool

    exactIdentityOnImLAbsRecordedIsTrue :
      exactIdentityOnImLAbsRecorded ≡ true

    identitySurfaceAudited :
      Bool

    identitySurfaceAuditedIsTrue :
      identitySurfaceAudited ≡ true

    endpointConfusionGuarded :
      Bool

    endpointConfusionGuardedIsTrue :
      endpointConfusionGuarded ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool

    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    orcslpgf :
      NSTriadSignedLaplacianIdentityReceiptORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadSignedLaplacianIdentityReceiptORCSLPGF

    statement :
      String

    statementIsCanonical :
      statement ≡
      "Candidate-only NS triad signed-operator identity receipt: on im(L_abs), L_signed_norm = I - 2 K_N is recorded with the L_abs, L_neg, and L_signed naming cleanup, exact endpoint confusion is guarded against, and theorem/full-NS/Clay promotion stays false."

open NSTriadSignedLaplacianIdentityReceipt public

canonicalNSTriadSignedLaplacianIdentityReceipt :
  NSTriadSignedLaplacianIdentityReceipt
canonicalNSTriadSignedLaplacianIdentityReceipt =
  mkNSTriadSignedLaplacianIdentityReceipt
    candidateSignedOperatorIdentityRecorded
    refl
    canonicalNSTriadSignedLaplacianIdentityAssumptions
    refl
    6
    refl
    canonicalNSTriadSignedLaplacianIdentityBlockers
    refl
    4
    refl
    candidateSignedOperatorIdentityText
    refl
    endpointConfusionGuardText
    refl
    auditModeText
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalNSTriadSignedLaplacianIdentityReceiptORCSLPGF
    refl
    "Candidate-only NS triad signed-operator identity receipt: on im(L_abs), L_signed_norm = I - 2 K_N is recorded with the L_abs, L_neg, and L_signed naming cleanup, exact endpoint confusion is guarded against, and theorem/full-NS/Clay promotion stays false."
    refl
