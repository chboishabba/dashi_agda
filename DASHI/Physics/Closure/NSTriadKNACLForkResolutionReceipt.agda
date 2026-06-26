module DASHI.Physics.Closure.NSTriadKNACLForkResolutionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed fork-resolution receipt for the mixed-tail ACL route.
--
-- This receipt records the decisive half-sum audit: the corrected ACL first
-- harmonic cancels exactly in signed form, but leaves the positive block at
-- half of the absolute mass.  Therefore the signed ACL lane cannot control the
-- current positive-sector Schur block, and the surviving route is direct
-- positive-sector magnitude/counting control.

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the NS triad K_N ACL fork resolution."

canonicalDocPath : String
canonicalDocPath =
  "docs/ns_triad_kn_after_acl_fork_resolution.md"

canonicalArtifactJSON : String
canonicalArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_signed_half_sum_proof_20260624/summary.json"

canonicalArtifactMarkdown : String
canonicalArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_acl_signed_half_sum_proof_20260624/summary.md"

canonicalReadoutText : String
canonicalReadoutText =
  "Fork A is dead. The corrected ACL first harmonic cancels exactly in signed form on the sampled same-shell transverse sets, but the positive block remains S_+ = S_abs/2, so signed ACL cancellation does not control the positive-sector Schur block. The live route is direct positive-sector magnitude/counting control only."

record NSTriadKNACLForkResolutionReceipt : Setω where
  constructor mkNSTriadKNACLForkResolutionReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNACLForkResolutionReceipt"

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

    aclSignedCancellationExact : Bool
    aclSignedCancellationExactIsTrue :
      aclSignedCancellationExact ≡ true

    forkADead : Bool
    forkADeadIsTrue :
      forkADead ≡ true

    forkBDirectPositiveSectorOnly : Bool
    forkBDirectPositiveSectorOnlyIsTrue :
      forkBDirectPositiveSectorOnly ≡ true

    positiveBlockControlledByACL : Bool
    positiveBlockControlledByACLIsFalse :
      positiveBlockControlledByACL ≡ false

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

open NSTriadKNACLForkResolutionReceipt public

canonicalNSTriadKNACLForkResolutionReceipt :
  NSTriadKNACLForkResolutionReceipt
canonicalNSTriadKNACLForkResolutionReceipt =
  mkNSTriadKNACLForkResolutionReceipt
    "NSTriadKNACLForkResolutionReceipt"
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
