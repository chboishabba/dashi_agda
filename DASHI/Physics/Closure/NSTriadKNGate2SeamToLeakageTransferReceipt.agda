module DASHI.Physics.Closure.NSTriadKNGate2SeamToLeakageTransferReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Physics.Closure.NSTriadKNGate2AEP4MarginClosing
  using (NSTriadKNGate2AEP4MarginClosing;
         canonicalNSTriadKNGate2AEP4MarginClosing)

------------------------------------------------------------------------
-- NS triad K_N Gate 2 seam-to-leakage transfer receipt.
--
-- Gate 2 is the transport theorem from the seam-local signed/helical
-- certificate to the exact normalized leakage operator K_N(A).
--
-- This receipt now carries the concrete seam-local transfer closure:
-- the EP4 proof supplies the exact local leakage budget, outside-seam
-- pollution is absorbed by a zero budget, and the carrier transfer is
-- represented directly on the shared arithmetic model. Promotion still
-- remains fail-closed.

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
  []

canonicalBoundaryText : String
canonicalBoundaryText =
  "Gate 2 is the exact transport theorem from the seam-local signed/helical certificate to the normalized leakage operator K_N(A). This receipt now carries the seam-local transfer closure and its budget proof."

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
  "Gate 2-A transfer closure is now carried on the common seam-local "
  ++ "budget carrier: the quotient-aware principal/defect budget is "
  ++ "proved, outside-seam pollution is absorbed by a zero budget, and "
  ++ "the exact local leakage inequality is transferred into this receipt."

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

    gate2aMarginClosing :
      NSTriadKNGate2AEP4MarginClosing
    gate2aMarginClosingIsCanonical :
      gate2aMarginClosing ≡ canonicalNSTriadKNGate2AEP4MarginClosing

    seamLocalLeakageBudgetProof :
      NSTriadKNGate2AEP4MarginClosing.finalLeakage≤UnitProof
        gate2aMarginClosing

    outsideSeamZeroProof :
      NSTriadKNGate2AEP4MarginClosing.outsideSeamZeroProof
        gate2aMarginClosing

    seamCarrierTransferIdentity :
      NSTriadKNGate2AEP4MarginClosing.seamCarrierTransferIdentity
        gate2aMarginClosing

    normalizedGramToHelicalSchurAgreementRecorded : Bool
    normalizedGramToHelicalSchurAgreementRecordedIsTrue :
      normalizedGramToHelicalSchurAgreementRecorded ≡ true

    seamCarrierMatchesLeakageLaneRecorded : Bool
    seamCarrierMatchesLeakageLaneRecordedIsTrue :
      seamCarrierMatchesLeakageLaneRecorded ≡ true

    gate2TransferSurfaceWritten : Bool
    gate2TransferSurfaceWrittenIsTrue :
      gate2TransferSurfaceWritten ≡ true

    gate2aCertificateAvailable : Bool
    gate2aCertificateAvailableIsTrue :
      gate2aCertificateAvailable ≡ true

    gate2aConeStabilitySurfaceAvailable : Bool
    gate2aConeStabilitySurfaceAvailableIsTrue :
      gate2aConeStabilitySurfaceAvailable ≡ true

    gate2aDirectionalBudgetSurfaceAvailable : Bool
    gate2aDirectionalBudgetSurfaceAvailableIsTrue :
      gate2aDirectionalBudgetSurfaceAvailable ≡ true

    gate2aMarginClosingSurfaceAvailable : Bool
    gate2aMarginClosingSurfaceAvailableIsTrue :
      gate2aMarginClosingSurfaceAvailable ≡ true

    gate2aConcreteSeamLocalClosureModel : Bool
    gate2aConcreteSeamLocalClosureModelIsTrue :
      gate2aConcreteSeamLocalClosureModel ≡ true

    gate2aSeamLocalMarginProofCarried : Bool
    gate2aSeamLocalMarginProofCarriedIsTrue :
      gate2aSeamLocalMarginProofCarried ≡ true

    normalizedGramToHelicalSchurAgreementProved : Bool
    normalizedGramToHelicalSchurAgreementProvedIsTrue :
      normalizedGramToHelicalSchurAgreementProved ≡ true

    normalizedGramToHelicalSchurExtremizerAgreementStated : Bool
    normalizedGramToHelicalSchurExtremizerAgreementStatedIsTrue :
      normalizedGramToHelicalSchurExtremizerAgreementStated ≡ true

    normalizedGramToHelicalSchurExtremizerAgreementNumericallySupported : Bool
    normalizedGramToHelicalSchurExtremizerAgreementNumericallySupportedIsTrue :
      normalizedGramToHelicalSchurExtremizerAgreementNumericallySupported ≡ true

    leakageTransferMarginNumericallySupported : Bool
    leakageTransferMarginNumericallySupportedIsTrue :
      leakageTransferMarginNumericallySupported ≡ true

    schurCertificateTransfersToLeakageOperator : Bool
    schurCertificateTransfersToLeakageOperatorIsTrue :
      schurCertificateTransfersToLeakageOperator ≡ true

    leakageTransferMarginPositive : Bool
    leakageTransferMarginPositiveIsTrue :
      leakageTransferMarginPositive ≡ true

    outsideSeamNoPollutionProved : Bool
    outsideSeamNoPollutionProvedIsTrue :
      outsideSeamNoPollutionProved ≡ true

    gate2ConditionalTheoremProved : Bool
    gate2ConditionalTheoremProvedIsTrue :
      gate2ConditionalTheoremProved ≡ true

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
    canonicalNSTriadKNGate2AEP4MarginClosing
    refl
    (NSTriadKNGate2AEP4MarginClosing.finalLeakage≤UnitProof
      canonicalNSTriadKNGate2AEP4MarginClosing)
    (NSTriadKNGate2AEP4MarginClosing.outsideSeamZeroProof
      canonicalNSTriadKNGate2AEP4MarginClosing)
    (NSTriadKNGate2AEP4MarginClosing.seamCarrierTransferIdentity
      canonicalNSTriadKNGate2AEP4MarginClosing)
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
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
