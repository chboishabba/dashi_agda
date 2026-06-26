module DASHI.Physics.Closure.NSTriadKNExactAlgebraicDefinitionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the exact algebraic definition of the NS triad K_N(A) Gram object."

canonicalDocPath : String
canonicalDocPath =
  "docs/ns_triad_kn_KN_exact_algebraic_definition.md"

canonicalMatrixFreeScriptPath : String
canonicalMatrixFreeScriptPath =
  "scripts/ns_triad_kn_matrix_free_operator.py"

canonicalExactIdentityScriptPath : String
canonicalExactIdentityScriptPath =
  "scripts/ns_triad_kn_exact_identity_scan.py"

canonicalLiveObject : String
canonicalLiveObject =
  "K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)"

canonicalAbsoluteOperator : String
canonicalAbsoluteOperator =
  "L_abs(A) = B_N^T W_abs(A) B_N"

canonicalNegativeOperator : String
canonicalNegativeOperator =
  "L_neg(A) = B_N^T W_neg(A) B_N"

canonicalNormalizationRead : String
canonicalNormalizationRead =
  "Normalization: A_m = sqrt(max(p_m, 0)), triad weight A_i A_j A_k, pair split 1/3 across the three unordered pairs, sign split by max(±gamma_t, 0), and positive-subspace conjugation by L_abs(A)^(-1/2)."

canonicalScriptMatchStatus : String
canonicalScriptMatchStatus =
  "candidate_checked"

record NSTriadKNExactAlgebraicDefinitionReceipt : Setω where
  constructor mkNSTriadKNExactAlgebraicDefinitionReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNExactAlgebraicDefinitionReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    docPath : String
    docPathIsCanonical :
      docPath ≡ canonicalDocPath

    matrixFreeScriptPath : String
    matrixFreeScriptPathIsCanonical :
      matrixFreeScriptPath ≡ canonicalMatrixFreeScriptPath

    exactIdentityScriptPath : String
    exactIdentityScriptPathIsCanonical :
      exactIdentityScriptPath ≡ canonicalExactIdentityScriptPath

    liveObject : String
    liveObjectIsCanonical :
      liveObject ≡ canonicalLiveObject

    absoluteOperator : String
    absoluteOperatorIsCanonical :
      absoluteOperator ≡ canonicalAbsoluteOperator

    negativeOperator : String
    negativeOperatorIsCanonical :
      negativeOperator ≡ canonicalNegativeOperator

    normalizationRead : String
    normalizationReadIsCanonical :
      normalizationRead ≡ canonicalNormalizationRead

    scriptObjectMatchStatus : String
    scriptObjectMatchStatusIsCanonical :
      scriptObjectMatchStatus ≡ canonicalScriptMatchStatus

    exactKDefinitionWritten : Bool
    exactKDefinitionWrittenIsTrue :
      exactKDefinitionWritten ≡ true

    scriptObjectMatched : Bool
    scriptObjectMatchedIsTrue :
      scriptObjectMatched ≡ true

    diagonalMassLemmaClosed : Bool
    diagonalMassLemmaClosedIsFalse :
      diagonalMassLemmaClosed ≡ false

    coherenceLemmaClosed : Bool
    coherenceLemmaClosedIsFalse :
      coherenceLemmaClosed ≡ false

    admissibleProfileLemmaClosed : Bool
    admissibleProfileLemmaClosedIsFalse :
      admissibleProfileLemmaClosed ≡ false

    gramCoercivityClosed : Bool
    gramCoercivityClosedIsFalse :
      gramCoercivityClosed ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNExactAlgebraicDefinitionReceipt public

canonicalNSTriadKNExactAlgebraicDefinitionReceipt :
  NSTriadKNExactAlgebraicDefinitionReceipt
canonicalNSTriadKNExactAlgebraicDefinitionReceipt =
  mkNSTriadKNExactAlgebraicDefinitionReceipt
    "NSTriadKNExactAlgebraicDefinitionReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalDocPath
    refl
    canonicalMatrixFreeScriptPath
    refl
    canonicalExactIdentityScriptPath
    refl
    canonicalLiveObject
    refl
    canonicalAbsoluteOperator
    refl
    canonicalNegativeOperator
    refl
    canonicalNormalizationRead
    refl
    canonicalScriptMatchStatus
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
    false
    refl
    false
    refl
    false
    refl
    false
    refl
