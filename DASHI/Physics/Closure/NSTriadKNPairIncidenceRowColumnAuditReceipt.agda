module DASHI.Physics.Closure.NSTriadKNPairIncidenceRowColumnAuditReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed receipt for the exact scripted row/column audit.

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the NS triad exact scripted pair-incidence row/column audit."

canonicalArtifactJSON : String
canonicalArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_pair_incidence_row_column_audit_20260625/summary.json"

canonicalArtifactMarkdown : String
canonicalArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_pair_incidence_row_column_audit_20260625/summary.md"

canonicalReadoutText : String
canonicalReadoutText =
  "Row/column audit status: under the checked exact-script normalization, the forced-tail family has row_sum_sup approximately constant and column_sum_sup approximately N^-2, while the uniform-geometry adversarial family has row_sum_sup approximately N^-2 and column_sum_sup approximately N^-1. Those asymmetries are compatible with a weighted Schur product route R_N(w_N) * C_N(w_N) <= C^2 / N^2, but that theorem is not yet proved."

record NSTriadKNPairIncidenceRowColumnAuditReceipt : Setω where
  constructor mkNSTriadKNPairIncidenceRowColumnAuditReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNPairIncidenceRowColumnAuditReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    artifactJSON : String
    artifactJSONIsCanonical :
      artifactJSON ≡ canonicalArtifactJSON

    artifactMarkdown : String
    artifactMarkdownIsCanonical :
      artifactMarkdown ≡ canonicalArtifactMarkdown

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    weightedSchurProductRouteStated : Bool
    weightedSchurProductRouteStatedIsTrue :
      weightedSchurProductRouteStated ≡ true

    forcedTailAsymmetryCompatibleObserved : Bool
    forcedTailAsymmetryCompatibleObservedIsTrue :
      forcedTailAsymmetryCompatibleObserved ≡ true

    adversarialAsymmetryCompatibleObserved : Bool
    adversarialAsymmetryCompatibleObservedIsTrue :
      adversarialAsymmetryCompatibleObserved ≡ true

    exactScriptConstantColumnClaimValidated : Bool
    exactScriptConstantColumnClaimValidatedIsFalse :
      exactScriptConstantColumnClaimValidated ≡ false

    uniformProfileIndependentBoundClosed : Bool
    uniformProfileIndependentBoundClosedIsFalse :
      uniformProfileIndependentBoundClosed ≡ false

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

open NSTriadKNPairIncidenceRowColumnAuditReceipt public

canonicalNSTriadKNPairIncidenceRowColumnAuditReceipt :
  NSTriadKNPairIncidenceRowColumnAuditReceipt
canonicalNSTriadKNPairIncidenceRowColumnAuditReceipt =
  mkNSTriadKNPairIncidenceRowColumnAuditReceipt
    "NSTriadKNPairIncidenceRowColumnAuditReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalArtifactJSON
    refl
    canonicalArtifactMarkdown
    refl
    canonicalReadoutText
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
    false
    refl
    false
    refl
    false
    refl
