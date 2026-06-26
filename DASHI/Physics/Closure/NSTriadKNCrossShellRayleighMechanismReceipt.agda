module DASHI.Physics.Closure.NSTriadKNCrossShellRayleighMechanismReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the NS triad cross-shell Rayleigh mechanism boundary."

canonicalDocPath : String
canonicalDocPath =
  "docs/ns_triad_kn_cross_shell_rayleigh_mechanism.md"

canonicalAuditScriptPath : String
canonicalAuditScriptPath =
  "scripts/ns_triad_kn_gram_rayleigh_margin_audit.py"

canonicalMechanismRead : String
canonicalMechanismRead =
  "Sampled worst-direction support localizes on the low-high-high 1-(N-1)-N seam, where the Biot-Savart factor carries a natural 1/N scale."

canonicalNonTheoremRead : String
canonicalNonTheoremRead =
  "The 1/N Biot-Savart factor identifies a candidate mechanism only; it does not by itself prove lambda_min(K_N(A)) >= c / N."

canonicalBlockTarget : String
canonicalBlockTarget =
  "Next theorem target: prove a Rayleigh lower bound on the 1-(N-1)-N block and show no other block is worse."

record NSTriadKNCrossShellRayleighMechanismReceipt : Setω where
  constructor mkNSTriadKNCrossShellRayleighMechanismReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNCrossShellRayleighMechanismReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    docPath : String
    docPathIsCanonical :
      docPath ≡ canonicalDocPath

    auditScriptPath : String
    auditScriptPathIsCanonical :
      auditScriptPath ≡ canonicalAuditScriptPath

    mechanismRead : String
    mechanismReadIsCanonical :
      mechanismRead ≡ canonicalMechanismRead

    nonTheoremRead : String
    nonTheoremReadIsCanonical :
      nonTheoremRead ≡ canonicalNonTheoremRead

    blockTarget : String
    blockTargetIsCanonical :
      blockTarget ≡ canonicalBlockTarget

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

open NSTriadKNCrossShellRayleighMechanismReceipt public

canonicalNSTriadKNCrossShellRayleighMechanismReceipt :
  NSTriadKNCrossShellRayleighMechanismReceipt
canonicalNSTriadKNCrossShellRayleighMechanismReceipt =
  mkNSTriadKNCrossShellRayleighMechanismReceipt
    "NSTriadKNCrossShellRayleighMechanismReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalDocPath
    refl
    canonicalAuditScriptPath
    refl
    canonicalMechanismRead
    refl
    canonicalNonTheoremRead
    refl
    canonicalBlockTarget
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
