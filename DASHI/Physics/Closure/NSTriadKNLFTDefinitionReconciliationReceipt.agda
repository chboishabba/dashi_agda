module DASHI.Physics.Closure.NSTriadKNLFTDefinitionReconciliationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed receipt for the sampled-Schur-object / bare-proxy reconciliation.
--
-- This receipt records that the sampled Schur-test matrix is not the same
-- object as the separate bare positive shell-geometry proxy. The empirical
-- sampled witness therefore remains candidate-only until a theorem carrier is
-- matched to the exact reconstructed operator.

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the NS triad K_N L_FT^+ definition reconciliation."

canonicalDocPath : String
canonicalDocPath =
  "docs/ns_triad_kn_lft_definition_reconciliation.md"

canonicalArtifactJSON : String
canonicalArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_definition_reconciliation_20260624/summary.json"

canonicalArtifactMarkdown : String
canonicalArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_definition_reconciliation_20260624/summary.md"

canonicalReadoutText : String
canonicalReadoutText =
  "Definition reconciliation status: different_object. The sampled Schur-test matrix reconstructed from pair-incidence weights is not the same object as the separate bare positive shell-geometry proxy G_+(k,p)=max(cos(theta_kp),0)*|k x p|/|k|^2 on the sampled mixed-tail shells, so the sampled N^-1 witness remains candidate-only and cannot yet be used as theorem evidence for the bare positive-sector geometry."

record NSTriadKNLFTDefinitionReconciliationReceipt : Setω where
  constructor mkNSTriadKNLFTDefinitionReconciliationReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNLFTDefinitionReconciliationReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    docPath : String
    docPathIsCanonical :
      docPath ≡ canonicalDocPath

    artifactJSON : String
    artifactJSONIsCanonical :
      artifactJSON ≡ canonicalArtifactJSON

    artifactMarkdown : String
    artifactMarkdownIsCanonical :
      artifactMarkdown ≡ canonicalArtifactMarkdown

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    verdict : String
    verdictIsCanonical :
      verdict ≡ "different_object"

    sameObject : Bool
    sameObjectIsFalse :
      sameObject ≡ false

    normalizedSameObject : Bool
    normalizedSameObjectIsFalse :
      normalizedSameObject ≡ false

    differentObject : Bool
    differentObjectIsTrue :
      differentObject ≡ true

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

open NSTriadKNLFTDefinitionReconciliationReceipt public

canonicalNSTriadKNLFTDefinitionReconciliationReceipt :
  NSTriadKNLFTDefinitionReconciliationReceipt
canonicalNSTriadKNLFTDefinitionReconciliationReceipt =
  mkNSTriadKNLFTDefinitionReconciliationReceipt
    "NSTriadKNLFTDefinitionReconciliationReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalDocPath
    refl
    canonicalArtifactJSON
    refl
    canonicalArtifactMarkdown
    refl
    canonicalReadoutText
    refl
    "different_object"
    refl
    false
    refl
    false
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
