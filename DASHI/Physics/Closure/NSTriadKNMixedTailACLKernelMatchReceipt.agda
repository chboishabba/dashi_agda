module DASHI.Physics.Closure.NSTriadKNMixedTailACLKernelMatchReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed receipt for the exact L_FT^+ / ACL kernel match audit.
--
-- This receipt records that the current mixed-tail positive-sector cross block
-- is not the Fields ACL kernel up to an N-only normalization: the exact entry
-- depends on profile amplitudes and on max(cos(closure), 0), so the signed ACL
-- cancellation factor does not survive entrywise.

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed receipt for the NS triad mixed-tail L_FT^+ / ACL kernel match audit."

canonicalKernelMatchDocPath : String
canonicalKernelMatchDocPath =
  "docs/ns_triad_kn_LFT_kernel_ACL_match.md"

canonicalKernelMatchArtifactJSON : String
canonicalKernelMatchArtifactJSON =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_kernel_acl_match_20260624/summary.json"

canonicalKernelMatchArtifactMarkdown : String
canonicalKernelMatchArtifactMarkdown =
  "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/ns_triad_kn_lft_kernel_acl_match_20260624/summary.md"

canonicalExactDashiKernelText : String
canonicalExactDashiKernelText =
  "L_FT^+(k,p) is assembled from pair-incidence sums of sqrt(pi_i*pi_j*pi_l)/3 * max(cos(phi_i+phi_j-phi_l),0)."

canonicalACLKernelText : String
canonicalACLKernelText =
  "The ACL carrier is a profile-independent signed/angular geometric factor, not a positive-sector profile-weighted kernel."

canonicalReadoutText : String
canonicalReadoutText =
  "Kernel match status: failed. The exact mixed-tail L_FT^+ entry carries profile amplitudes and positive-sector truncation, so the current DASHI cross block does not equal the Fields ACL kernel up to an N-only normalization. Positive-sector and absolute-sector ACL survival are both false, the Schur lift is unavailable on this route, and theorem/Clay promotion remain false."

record NSTriadKNMixedTailACLKernelMatchReceipt : Setω where
  constructor mkNSTriadKNMixedTailACLKernelMatchReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNMixedTailACLKernelMatchReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    kernelMatchDocPath : String
    kernelMatchDocPathIsCanonical :
      kernelMatchDocPath ≡ canonicalKernelMatchDocPath

    kernelMatchArtifactJSON : String
    kernelMatchArtifactJSONIsCanonical :
      kernelMatchArtifactJSON ≡ canonicalKernelMatchArtifactJSON

    kernelMatchArtifactMarkdown : String
    kernelMatchArtifactMarkdownIsCanonical :
      kernelMatchArtifactMarkdown ≡ canonicalKernelMatchArtifactMarkdown

    exactDashiKernelText : String
    exactDashiKernelTextIsCanonical :
      exactDashiKernelText ≡ canonicalExactDashiKernelText

    aclKernelText : String
    aclKernelTextIsCanonical :
      aclKernelText ≡ canonicalACLKernelText

    readoutText : String
    readoutTextIsCanonical :
      readoutText ≡ canonicalReadoutText

    exactDashiLFTKernelWritten : Bool
    exactDashiLFTKernelWrittenIsTrue :
      exactDashiLFTKernelWritten ≡ true

    aclKernelWritten : Bool
    aclKernelWrittenIsTrue :
      aclKernelWritten ≡ true

    kernelMatchStatus : String
    kernelMatchStatusIsCanonical :
      kernelMatchStatus ≡ "failed"

    positiveSectorSurvivesACL : Bool
    positiveSectorSurvivesACLIsFalse :
      positiveSectorSurvivesACL ≡ false

    absoluteSectorSurvivesACL : Bool
    absoluteSectorSurvivesACLIsFalse :
      absoluteSectorSurvivesACL ≡ false

    schurLiftAvailable : Bool
    schurLiftAvailableIsFalse :
      schurLiftAvailable ≡ false

    profileIndependentBoundClosed : Bool
    profileIndependentBoundClosedIsFalse :
      profileIndependentBoundClosed ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNMixedTailACLKernelMatchReceipt public

canonicalNSTriadKNMixedTailACLKernelMatchReceipt :
  NSTriadKNMixedTailACLKernelMatchReceipt
canonicalNSTriadKNMixedTailACLKernelMatchReceipt =
  mkNSTriadKNMixedTailACLKernelMatchReceipt
    "NSTriadKNMixedTailACLKernelMatchReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalKernelMatchDocPath
    refl
    canonicalKernelMatchArtifactJSON
    refl
    canonicalKernelMatchArtifactMarkdown
    refl
    canonicalExactDashiKernelText
    refl
    canonicalACLKernelText
    refl
    canonicalReadoutText
    refl
    true
    refl
    true
    refl
    "failed"
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
