module DASHI.Physics.Closure.NSTriadKNGramRayleighMarginAuditReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the NS triad K_N(A) Rayleigh-margin audit."

canonicalScriptPath : String
canonicalScriptPath =
  "scripts/ns_triad_kn_gram_rayleigh_margin_audit.py"

canonicalSummaryPath : String
canonicalSummaryPath =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_gram_rayleigh_margin_audit_20260625/summary.json"

canonicalQuestion : String
canonicalQuestion =
  "Is the sampled lambda_min floor protected by diagonal dominance, frame incoherence, profile spreading, or a mixed mechanism?"

canonicalFailClosedRead : String
canonicalFailClosedRead =
  "The sampled receipts expose Rayleigh margin proxies and dominant shell-pair contributions, but not a closed finite sign/profile cell theorem."

record NSTriadKNGramRayleighMarginAuditReceipt : Setω where
  constructor mkNSTriadKNGramRayleighMarginAuditReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNGramRayleighMarginAuditReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    scriptPath : String
    scriptPathIsCanonical :
      scriptPath ≡ canonicalScriptPath

    summaryPath : String
    summaryPathIsCanonical :
      summaryPath ≡ canonicalSummaryPath

    question : String
    questionIsCanonical :
      question ≡ canonicalQuestion

    failClosedRead : String
    failClosedReadIsCanonical :
      failClosedRead ≡ canonicalFailClosedRead

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

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGramRayleighMarginAuditReceipt public

canonicalNSTriadKNGramRayleighMarginAuditReceipt :
  NSTriadKNGramRayleighMarginAuditReceipt
canonicalNSTriadKNGramRayleighMarginAuditReceipt =
  mkNSTriadKNGramRayleighMarginAuditReceipt
    "NSTriadKNGramRayleighMarginAuditReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalScriptPath
    refl
    canonicalSummaryPath
    refl
    canonicalQuestion
    refl
    canonicalFailClosedRead
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
