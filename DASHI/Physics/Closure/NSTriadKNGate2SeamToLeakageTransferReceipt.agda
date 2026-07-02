module DASHI.Physics.Closure.NSTriadKNGate2SeamToLeakageTransferReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS triad K_N Gate 2 seam-to-leakage transfer receipt.
--
-- Gate 2 is the transport theorem from the seam-local signed/helical
-- certificate to the exact normalized leakage operator K_N(A).
--
-- This receipt is fail-closed. It records the exact downstream object,
-- the transfer obligations, and the fact that none of the transfer
-- booleans are yet proved.

data NSTriadKNGate2TransferStatus : Set where
  gate2TransferRecorded :
    NSTriadKNGate2TransferStatus

data NSTriadKNGate2TransferOpenObligation : Set where
  normalizedGramToHelicalSchurAgreementOpen :
    NSTriadKNGate2TransferOpenObligation
  schurCertificateTransfersToLeakageOperatorOpen :
    NSTriadKNGate2TransferOpenObligation
  leakageTransferMarginPositiveOpen :
    NSTriadKNGate2TransferOpenObligation
  outsideSeamNoPollutionOpen :
    NSTriadKNGate2TransferOpenObligation
  gate2ConditionalTheoremOpen :
    NSTriadKNGate2TransferOpenObligation

canonicalNSTriadKNGate2TransferOpenObligations :
  List NSTriadKNGate2TransferOpenObligation
canonicalNSTriadKNGate2TransferOpenObligations =
  normalizedGramToHelicalSchurAgreementOpen
  ∷ schurCertificateTransfersToLeakageOperatorOpen
  ∷ leakageTransferMarginPositiveOpen
  ∷ outsideSeamNoPollutionOpen
  ∷ gate2ConditionalTheoremOpen
  ∷ []

canonicalBoundaryText : String
canonicalBoundaryText =
  "Gate 2 is the exact transport theorem from the seam-local signed/helical certificate to the normalized leakage operator K_N(A). This receipt records the transfer surface only."

canonicalExactLeakageObjectText : String
canonicalExactLeakageObjectText =
  "Exact downstream object: K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2), using the canonical amplitude-weighted pair-incidence normalization."

canonicalUpstreamCarrierText : String
canonicalUpstreamCarrierText =
  "Upstream Gate 1 carrier: on the seam block C, S_C = L_good - L_bad and equivalently Q_N = 2 L_good - 3 L_bad on 1_C^perp."

canonicalTransferShapeText : String
canonicalTransferShapeText =
  "Gate 2 target shape: seam Schur/helical PSD-domination implies the exact K_N(A) cross-shell leakage contraction used downstream, with strict margin preserved uniformly in N."

canonicalOpenObligationsText : String
canonicalOpenObligationsText =
  "Open transfer obligations: normalization agreement, exact Schur-to-leakage transport, margin preservation under all constants, and no outside-seam pollution."

canonicalSourcesText : String
canonicalSourcesText =
  "Sources: docs/ns_triad_kn_KN_exact_algebraic_definition.md, docs/ns_triad_kn_cross_shell_signed_domination.md, docs/ns_triad_kn_cross_shell_leakage_bound.md, docs/ns_triad_kn_gram_coercivity_target.md."

record NSTriadKNGate2SeamToLeakageTransferReceipt : Setω where
  constructor mkNSTriadKNGate2SeamToLeakageTransferReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNGate2SeamToLeakageTransferReceipt"

    status : NSTriadKNGate2TransferStatus
    statusIsCanonical :
      status ≡ gate2TransferRecorded

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    exactLeakageObjectText : String
    exactLeakageObjectTextIsCanonical :
      exactLeakageObjectText ≡ canonicalExactLeakageObjectText

    upstreamCarrierText : String
    upstreamCarrierTextIsCanonical :
      upstreamCarrierText ≡ canonicalUpstreamCarrierText

    transferShapeText : String
    transferShapeTextIsCanonical :
      transferShapeText ≡ canonicalTransferShapeText

    openObligationsText : String
    openObligationsTextIsCanonical :
      openObligationsText ≡ canonicalOpenObligationsText

    sourcesText : String
    sourcesTextIsCanonical :
      sourcesText ≡ canonicalSourcesText

    docPath : String
    docPathIsCanonical :
      docPath ≡ "docs/ns_triad_kn_gate2_seam_to_leakage_transfer.md"

    normalizedGramToHelicalSchurAgreementRecorded : Bool
    normalizedGramToHelicalSchurAgreementRecordedIsTrue :
      normalizedGramToHelicalSchurAgreementRecorded ≡ true

    seamCarrierMatchesLeakageLaneRecorded : Bool
    seamCarrierMatchesLeakageLaneRecordedIsTrue :
      seamCarrierMatchesLeakageLaneRecorded ≡ true

    gate2TransferSurfaceWritten : Bool
    gate2TransferSurfaceWrittenIsTrue :
      gate2TransferSurfaceWritten ≡ true

    normalizedGramToHelicalSchurAgreementProved : Bool
    normalizedGramToHelicalSchurAgreementProvedIsFalse :
      normalizedGramToHelicalSchurAgreementProved ≡ false

    schurCertificateTransfersToLeakageOperator : Bool
    schurCertificateTransfersToLeakageOperatorIsFalse :
      schurCertificateTransfersToLeakageOperator ≡ false

    leakageTransferMarginPositive : Bool
    leakageTransferMarginPositiveIsFalse :
      leakageTransferMarginPositive ≡ false

    outsideSeamNoPollutionProved : Bool
    outsideSeamNoPollutionProvedIsFalse :
      outsideSeamNoPollutionProved ≡ false

    gate2ConditionalTheoremProved : Bool
    gate2ConditionalTheoremProvedIsFalse :
      gate2ConditionalTheoremProved ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGate2SeamToLeakageTransferReceipt public

canonicalNSTriadKNGate2SeamToLeakageTransferReceipt :
  NSTriadKNGate2SeamToLeakageTransferReceipt
canonicalNSTriadKNGate2SeamToLeakageTransferReceipt =
  mkNSTriadKNGate2SeamToLeakageTransferReceipt
    "NSTriadKNGate2SeamToLeakageTransferReceipt"
    refl
    gate2TransferRecorded
    refl
    canonicalBoundaryText
    refl
    canonicalExactLeakageObjectText
    refl
    canonicalUpstreamCarrierText
    refl
    canonicalTransferShapeText
    refl
    canonicalOpenObligationsText
    refl
    canonicalSourcesText
    refl
    "docs/ns_triad_kn_gate2_seam_to_leakage_transfer.md"
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
    false
    refl
    false
    refl
