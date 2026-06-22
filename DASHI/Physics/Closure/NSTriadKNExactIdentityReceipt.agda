module DASHI.Physics.Closure.NSTriadKNExactIdentityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed NS triad exact-identity receipt.
--
-- Corrected positive-subspace identity:
--
--   L_signed_norm = I - 2 K_N on im(L_abs)
--
-- This receipt records the corrected exact identity on the positive
-- subspace only.  The earlier large identity error is explicitly traced to
-- the wrong object and null-space misuse.  No theorem is claimed, and
-- theorem/full-NS/Clay promotion stays false.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNExactIdentityStatus : Set where
  correctedPositiveSubspaceIdentityRecorded :
    NSTriadKNExactIdentityStatus
  wrongObjectAndNullSpaceMisuseRecorded :
    NSTriadKNExactIdentityStatus
  identityShapeSeparatedFromProof :
    NSTriadKNExactIdentityStatus
  failClosedPromotionWallRecorded :
    NSTriadKNExactIdentityStatus

data NSTriadKNExactIdentityRow : Set where
  exactPositiveSubspaceIdentityRecorded :
    NSTriadKNExactIdentityRow
  positiveSubspaceImLAbsRecorded :
    NSTriadKNExactIdentityRow
  correctedFromWrongObjectRecorded :
    NSTriadKNExactIdentityRow
  nullSpaceMisuseRecorded :
    NSTriadKNExactIdentityRow
  failClosedPromotionWallRecorded :
    NSTriadKNExactIdentityRow

rowStatement : NSTriadKNExactIdentityRow → String
rowStatement exactPositiveSubspaceIdentityRecorded =
  "Target: record the corrected exact identity L_signed_norm = I - 2 K_N on im(L_abs)."
rowStatement positiveSubspaceImLAbsRecorded =
  "Target: keep the positive subspace im(L_abs) explicit as the domain of the identity."
rowStatement correctedFromWrongObjectRecorded =
  "Target: note that the earlier large identity error came from the wrong object."
rowStatement nullSpaceMisuseRecorded =
  "Target: note that the earlier large identity error also came from null-space misuse."
rowStatement failClosedPromotionWallRecorded =
  "Target: keep theorem, full-NS, and Clay promotion walls closed."

record NSTriadKNExactIdentityRowRecord : Set where
  field
    key :
      NSTriadKNExactIdentityRow
    statement :
      String
    statementIsCanonical :
      statement ≡ rowStatement key

canonicalNSTriadKNExactIdentityRows :
  List NSTriadKNExactIdentityRowRecord
canonicalNSTriadKNExactIdentityRows =
  record
    { key = exactPositiveSubspaceIdentityRecorded
    ; statement = rowStatement exactPositiveSubspaceIdentityRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = positiveSubspaceImLAbsRecorded
    ; statement = rowStatement positiveSubspaceImLAbsRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = correctedFromWrongObjectRecorded
    ; statement = rowStatement correctedFromWrongObjectRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = nullSpaceMisuseRecorded
    ; statement = rowStatement nullSpaceMisuseRecorded
    ; statementIsCanonical = refl
    }
  ∷ record
    { key = failClosedPromotionWallRecorded
    ; statement = rowStatement failClosedPromotionWallRecorded
    ; statementIsCanonical = refl
    }
  ∷ []

nstriadKNExactIdentityRowCount : Nat
nstriadKNExactIdentityRowCount =
  listLength canonicalNSTriadKNExactIdentityRows

nstriadKNExactIdentityRowCountIs5 :
  nstriadKNExactIdentityRowCount ≡ 5
nstriadKNExactIdentityRowCountIs5 =
  refl

data NSTriadKNExactIdentityGap : Set where
  exactIdentityIsCandidateOnly :
    NSTriadKNExactIdentityGap
  positiveSubspaceProofNotClaimed :
    NSTriadKNExactIdentityGap
  wrongObjectErrorCorrectedButNotPromoted :
    NSTriadKNExactIdentityGap
  nullSpaceMisuseSeparated :
    NSTriadKNExactIdentityGap
  theoremAndClayPromotionRemainFalse :
    NSTriadKNExactIdentityGap

canonicalNSTriadKNExactIdentityGaps :
  List NSTriadKNExactIdentityGap
canonicalNSTriadKNExactIdentityGaps =
  exactIdentityIsCandidateOnly
  ∷ positiveSubspaceProofNotClaimed
  ∷ wrongObjectErrorCorrectedButNotPromoted
  ∷ nullSpaceMisuseSeparated
  ∷ theoremAndClayPromotionRemainFalse
  ∷ []

nstriadKNExactIdentityGapCount : Nat
nstriadKNExactIdentityGapCount =
  listLength canonicalNSTriadKNExactIdentityGaps

nstriadKNExactIdentityGapCountIs5 :
  nstriadKNExactIdentityGapCount ≡ 5
nstriadKNExactIdentityGapCountIs5 =
  refl

canonicalTheoremShapeText : String
canonicalTheoremShapeText =
  "Corrected exact identity on the positive subspace: L_signed_norm = I - 2 K_N on im(L_abs)."

canonicalWrongObjectText : String
canonicalWrongObjectText =
  "Earlier large identity error: the wrong object was used."

canonicalNullSpaceMisuseText : String
canonicalNullSpaceMisuseText =
  "Earlier large identity error: null-space misuse was involved, and that misuse is corrected here."

canonicalOText : String
canonicalOText =
  "O: record the active NS triad exact-identity boundary as a fail-closed receipt."

canonicalRText : String
canonicalRText =
  "R: isolate the corrected exact identity on im(L_abs), and separate the wrong-object and null-space misuse corrections from any proof claim."

canonicalCText : String
canonicalCText =
  "C: expose canonical rows, gaps, theorem-shape text, and explicit false promotion gates."

canonicalSText : String
canonicalSText =
  "S: the positive-subspace identity is recorded as corrected exact shape only, while proof remains unclaimed."

canonicalLText : String
canonicalLText =
  "L: wrong object / null-space misuse -> corrected positive-subspace identity -> audited receipt -> no theorem promotion."

canonicalPText : String
canonicalPText =
  "P: keep L_signed_norm = I - 2 K_N on im(L_abs) candidate-only and do not promote theorem, full-NS, or Clay status."

canonicalGText : String
canonicalGText =
  "G: theorem, full-NS, and Clay promotion remain false."

canonicalFText : String
canonicalFText =
  "F: the missing evidence is a proof of the exact positive-subspace identity; the earlier error came from the wrong object and null-space misuse."

record NSTriadKNExactIdentityReceiptORCSLPGF : Set where
  constructor mkNSTriadKNExactIdentityReceiptORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ canonicalOText
    R : String
    RIsCanonical : R ≡ canonicalRText
    C : String
    CIsCanonical : C ≡ canonicalCText
    S : String
    SIsCanonical : S ≡ canonicalSText
    L : String
    LIsCanonical : L ≡ canonicalLText
    P : String
    PIsCanonical : P ≡ canonicalPText
    G : String
    GIsCanonical : G ≡ canonicalGText
    F : String
    FIsCanonical : F ≡ canonicalFText

open NSTriadKNExactIdentityReceiptORCSLPGF public

canonicalNSTriadKNExactIdentityReceiptORCSLPGF :
  NSTriadKNExactIdentityReceiptORCSLPGF
canonicalNSTriadKNExactIdentityReceiptORCSLPGF =
  mkNSTriadKNExactIdentityReceiptORCSLPGF
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

record NSTriadKNExactIdentityReceipt : Setω where
  constructor mkNSTriadKNExactIdentityReceipt
  field
    status :
      NSTriadKNExactIdentityStatus
    statusIsCanonical :
      status ≡ correctedPositiveSubspaceIdentityRecorded

    rows :
      List NSTriadKNExactIdentityRowRecord
    rowsAreCanonical :
      rows ≡ canonicalNSTriadKNExactIdentityRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nstriadKNExactIdentityRowCount

    gaps :
      List NSTriadKNExactIdentityGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadKNExactIdentityGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nstriadKNExactIdentityGapCount

    theoremShape :
      String
    theoremShapeIsCanonical :
      theoremShape ≡ canonicalTheoremShapeText

    wrongObjectCorrection :
      String
    wrongObjectCorrectionIsCanonical :
      wrongObjectCorrection ≡ canonicalWrongObjectText

    nullSpaceCorrection :
      String
    nullSpaceCorrectionIsCanonical :
      nullSpaceCorrection ≡ canonicalNullSpaceMisuseText

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    exactIdentityRecordedHere :
      Bool
    exactIdentityRecordedHereIsTrue :
      exactIdentityRecordedHere ≡ true

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
      NSTriadKNExactIdentityReceiptORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNExactIdentityReceiptORCSLPGF

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only NS triad exact-identity receipt: the corrected exact identity L_signed_norm = I - 2 K_N on im(L_abs) is recorded, the earlier wrong-object/null-space misuse is corrected, and theorem/full-NS/Clay promotion stays false."

open NSTriadKNExactIdentityReceipt public

canonicalNSTriadKNExactIdentityReceipt :
  NSTriadKNExactIdentityReceipt
canonicalNSTriadKNExactIdentityReceipt =
  mkNSTriadKNExactIdentityReceipt
    correctedPositiveSubspaceIdentityRecorded
    refl
    canonicalNSTriadKNExactIdentityRows
    refl
    nstriadKNExactIdentityRowCount
    refl
    canonicalNSTriadKNExactIdentityGaps
    refl
    nstriadKNExactIdentityGapCount
    refl
    canonicalTheoremShapeText
    refl
    canonicalWrongObjectText
    refl
    canonicalNullSpaceMisuseText
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
    canonicalNSTriadKNExactIdentityReceiptORCSLPGF
    refl
    "Candidate-only NS triad exact-identity receipt: the corrected exact identity L_signed_norm = I - 2 K_N on im(L_abs) is recorded, the earlier wrong-object/null-space misuse is corrected, and theorem/full-NS/Clay promotion stays false."
    refl
