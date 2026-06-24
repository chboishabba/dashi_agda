module DASHI.Physics.Closure.NSTriadKNPairIncidenceOperatorReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed receipt for the exact scripted pair-incidence operator.
--
-- This receipt records the single live NS triad Schur object after the ACL
-- kernel mismatch and bare-proxy reconciliation. The sampled N^-1 Schur
-- witness is retained only for the exact scripted pair-incidence operator.

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the NS triad exact scripted pair-incidence operator."

canonicalArtifactJSON : String
canonicalArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_pair_incidence_operator_proof_20260624/summary.json"

canonicalArtifactMarkdown : String
canonicalArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_pair_incidence_operator_proof_20260624/summary.md"

canonicalReconciliationArtifactJSON : String
canonicalReconciliationArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_definition_reconciliation_20260624/summary.json"

canonicalSampledSchurArtifactJSON : String
canonicalSampledSchurArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_schur_test_proof_20260624/summary.json"

canonicalOperatorName : String
canonicalOperatorName =
  "exact_scripted_pair_incidence_operator"

canonicalOperatorStatement : String
canonicalOperatorStatement =
  "The live NS triad Schur object is the exact scripted pair-incidence operator reconstructed from retained resonant triads on the finite-to-tail cross block."

canonicalOperatorFormula : String
canonicalOperatorFormula =
  "For a finite mode k and tail mode p, L_FT,script^+(k,p) is the negative sum over retained resonant triads whose pair-incidence edge joins k to p of (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0)."

canonicalReadoutText : String
canonicalReadoutText =
  "Live-object status: exact scripted pair-incidence operator only. The sampled Schur witness matches this exact scripted object on the recorded N=6,8,10,12 rows, while the reconciliation verdict remains different_object against the bare shell-geometry proxy. The uniform theorem target ||L_FT,script^N||_op <= C / N remains open, and theorem/full-NS/BKM/Clay promotion remain false."

canonicalTheoremTarget : String
canonicalTheoremTarget =
  "||L_FT,script^N||_op <= C / N"

record NSTriadKNPairIncidenceOperatorReceipt : Setω where
  constructor mkNSTriadKNPairIncidenceOperatorReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNPairIncidenceOperatorReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    artifactJSON : String
    artifactJSONIsCanonical :
      artifactJSON ≡ canonicalArtifactJSON

    artifactMarkdown : String
    artifactMarkdownIsCanonical :
      artifactMarkdown ≡ canonicalArtifactMarkdown

    reconciliationArtifactJSON : String
    reconciliationArtifactJSONIsCanonical :
      reconciliationArtifactJSON ≡ canonicalReconciliationArtifactJSON

    sampledSchurArtifactJSON : String
    sampledSchurArtifactJSONIsCanonical :
      sampledSchurArtifactJSON ≡ canonicalSampledSchurArtifactJSON

    operatorName : String
    operatorNameIsCanonical :
      operatorName ≡ canonicalOperatorName

    operatorStatement : String
    operatorStatementIsCanonical :
      operatorStatement ≡ canonicalOperatorStatement

    operatorFormula : String
    operatorFormulaIsCanonical :
      operatorFormula ≡ canonicalOperatorFormula

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    theoremTarget : String
    theoremTargetIsCanonical :
      theoremTarget ≡ canonicalTheoremTarget

    sampledSchurWitnessMatchesObject : Bool
    sampledSchurWitnessMatchesObjectIsTrue :
      sampledSchurWitnessMatchesObject ≡ true

    bareProxyReconciliationVerdict : String
    bareProxyReconciliationVerdictIsCanonical :
      bareProxyReconciliationVerdict ≡ "different_object"

    profileIndependentTheoremClosed : Bool
    profileIndependentTheoremClosedIsFalse :
      profileIndependentTheoremClosed ≡ false

    schurResidueScaleClosed : Bool
    schurResidueScaleClosedIsFalse :
      schurResidueScaleClosed ≡ false

    bkmResidenceBridgeClosed : Bool
    bkmResidenceBridgeClosedIsFalse :
      bkmResidenceBridgeClosed ≡ false

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

open NSTriadKNPairIncidenceOperatorReceipt public

canonicalNSTriadKNPairIncidenceOperatorReceipt :
  NSTriadKNPairIncidenceOperatorReceipt
canonicalNSTriadKNPairIncidenceOperatorReceipt =
  mkNSTriadKNPairIncidenceOperatorReceipt
    "NSTriadKNPairIncidenceOperatorReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalArtifactJSON
    refl
    canonicalArtifactMarkdown
    refl
    canonicalReconciliationArtifactJSON
    refl
    canonicalSampledSchurArtifactJSON
    refl
    canonicalOperatorName
    refl
    canonicalOperatorStatement
    refl
    canonicalOperatorFormula
    refl
    canonicalReadoutText
    refl
    canonicalTheoremTarget
    refl
    true
    refl
    "different_object"
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
