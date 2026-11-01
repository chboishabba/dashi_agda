module DASHI.Physics.Closure.NSTriadKNGramCoercivityTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed receipt for the live NS triad K_N(A) Gram-coercivity target.
--
-- This receipt records the post-Schur route correction:
--   * retired theorem carriers,
--   * the live amplitude-weighted Gram object,
--   * the Rayleigh-form theorem target,
--   * the four analytic proof obligations,
-- while keeping every promotion flag false.

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the live NS triad amplitude-weighted Gram-coercivity target."

canonicalDocPath : String
canonicalDocPath =
  "docs/ns_triad_kn_gram_coercivity_target.md"

canonicalDecompositionScriptPath : String
canonicalDecompositionScriptPath =
  "scripts/ns_triad_kn_gram_coercivity_decomposition.py"

canonicalDecompositionSummaryPath : String
canonicalDecompositionSummaryPath =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_gram_coercivity_decomposition_20260625/summary.json"

canonicalLiveObject : String
canonicalLiveObject =
  "K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)"

canonicalRayleighTarget : String
canonicalRayleighTarget =
  "lambda_min(K_N(A)) = inf_{|v|_2 = 1} <v, K_N(A) v>"

canonicalTheoremTarget : String
canonicalTheoremTarget =
  "<v, K_N(A) v> >= (c / N) * |v|_2^2 for all admissible A and v"

canonicalRetiredCarrier : String
canonicalRetiredCarrier =
  "Retired theorem carriers: positive-sector Schur norm route, ACL cancellation route, and bare L_FT^+ proxy route."

canonicalMeasuredRead : String
canonicalMeasuredRead =
  "Measured state: the exact scripted pair-incidence object is canonicalized and the sampled shell rows still show a positive Gram-side floor with small cross-block interference, but the c / N theorem scale is not promoted here."

canonicalLemma1 : String
canonicalLemma1 =
  "Lemma 1: K_N(A) exactness."

canonicalLemma2 : String
canonicalLemma2 =
  "Lemma 2: diagonal mass lower bound."

canonicalLemma3 : String
canonicalLemma3 =
  "Lemma 3: coherence / off-diagonal control."

canonicalLemma4 : String
canonicalLemma4 =
  "Lemma 4: admissible high-high profile condition."

record NSTriadKNGramCoercivityTargetReceipt : Setω where
  constructor mkNSTriadKNGramCoercivityTargetReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNGramCoercivityTargetReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    docPath : String
    docPathIsCanonical :
      docPath ≡ canonicalDocPath

    decompositionScriptPath : String
    decompositionScriptPathIsCanonical :
      decompositionScriptPath ≡ canonicalDecompositionScriptPath

    decompositionSummaryPath : String
    decompositionSummaryPathIsCanonical :
      decompositionSummaryPath ≡ canonicalDecompositionSummaryPath

    retiredCarrierRead : String
    retiredCarrierReadIsCanonical :
      retiredCarrierRead ≡ canonicalRetiredCarrier

    liveObject : String
    liveObjectIsCanonical :
      liveObject ≡ canonicalLiveObject

    measuredRead : String
    measuredReadIsCanonical :
      measuredRead ≡ canonicalMeasuredRead

    rayleighTarget : String
    rayleighTargetIsCanonical :
      rayleighTarget ≡ canonicalRayleighTarget

    theoremTarget : String
    theoremTargetIsCanonical :
      theoremTarget ≡ canonicalTheoremTarget

    lemma1 : String
    lemma1IsCanonical :
      lemma1 ≡ canonicalLemma1

    lemma2 : String
    lemma2IsCanonical :
      lemma2 ≡ canonicalLemma2

    lemma3 : String
    lemma3IsCanonical :
      lemma3 ≡ canonicalLemma3

    lemma4 : String
    lemma4IsCanonical :
      lemma4 ≡ canonicalLemma4

    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed : Bool
    failClosedIsTrue :
      failClosed ≡ true

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    bkmExclusionProved : Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGramCoercivityTargetReceipt public

canonicalNSTriadKNGramCoercivityTargetReceipt :
  NSTriadKNGramCoercivityTargetReceipt
canonicalNSTriadKNGramCoercivityTargetReceipt =
  mkNSTriadKNGramCoercivityTargetReceipt
    "NSTriadKNGramCoercivityTargetReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalDocPath
    refl
    canonicalDecompositionScriptPath
    refl
    canonicalDecompositionSummaryPath
    refl
    canonicalRetiredCarrier
    refl
    canonicalLiveObject
    refl
    canonicalMeasuredRead
    refl
    canonicalRayleighTarget
    refl
    canonicalTheoremTarget
    refl
    canonicalLemma1
    refl
    canonicalLemma2
    refl
    canonicalLemma3
    refl
    canonicalLemma4
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
