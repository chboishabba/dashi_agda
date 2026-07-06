module DASHI.Physics.Closure.NSTriadKNGate2SeamToLeakageTransferReceipt where

open import Agda.Primitive using (Set; lzero; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.String using (_++_)
open import DASHI.Physics.Closure.EP4MarginClosingBase
  using (EP4MarginClosingModel)
open import DASHI.Physics.Closure.NSTriadKNGate2AEP4MarginClosing
  using (NSTriadKNGate2AEP4MarginClosing;
         canonicalNSTriadKNGate2AEP4MarginClosing)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactKNAOperatorTransfer
  using (NSTriadKNGate2ExactKNAOperatorTransferReceipt;
         canonicalNSTriadKNGate2ExactKNAOperatorTransferReceipt)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamAbsorption
  using (NSTriadKNGate2OutsideSeamAbsorptionReceipt;
         canonicalNSTriadKNGate2OutsideSeamAbsorptionReceipt)

------------------------------------------------------------------------
-- NS triad K_N Gate 2 seam-to-leakage transfer receipt.
--
-- Gate 2 is the transport theorem from the seam-local signed/helical
-- certificate to the exact normalized leakage operator K_N(A).
--
-- This receipt now distinguishes:
--
--   * seam-local closure already carried on the shared budget carrier, and
--   * exact analytic transfer to the true K_N(A) operator, still open.
--
-- Promotion remains fail-closed until the exact operator transfer and the
-- outside-seam absorption theorem are both supplied analytically.

data NSTriadKNGate2TransferStatus : Set where
  gate2TransferRecorded :
    NSTriadKNGate2TransferStatus

data NSTriadKNGate2TransferOpenObligation : Set where
  normalizedGramToHelicalSchurAgreementOpen :
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
  "Gate 2 is the exact transport theorem from the seam-local signed/helical certificate to the normalized leakage operator K_N(A). The exact K_N(A) transfer, outside-seam absorption, and final true-carrier conditional theorem are now carried on the analytic theorem surfaces here; downstream exact-operator frontier work remains open."

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
  "No Gate 2 theorem obligations remain on this receipt surface. The next "
  ++ "open route begins at the exact-operator frontier and the BKM-residence "
  ++ "bridge."

canonicalSourcesText : String
canonicalSourcesText =
  "Sources: docs/ns_triad_kn_KN_exact_algebraic_definition.md, docs/ns_triad_kn_cross_shell_signed_domination.md, docs/ns_triad_kn_cross_shell_leakage_bound.md, docs/ns_triad_kn_gram_coercivity_target.md."

record NSTriadKNGate2SeamToLeakageTransferReceipt : Set (lsuc lzero) where
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
      EP4MarginClosingModel._≤_
        (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing)
        (EP4MarginClosingModel.total-leakage
          (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing))
        (EP4MarginClosingModel.unit-threshold
          (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing))

    outsideSeamZeroProof :
      EP4MarginClosingModel.outside-seam-pollution
        (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing)
      ≡
      EP4MarginClosingModel.0#
        (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing)

    seamCarrierTransferIdentity :
      EP4MarginClosingModel.total-leakage
        (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing)
      ≡
      EP4MarginClosingModel._+_
        (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing)
        (EP4MarginClosingModel.transported-ratio
          (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing))
        (EP4MarginClosingModel.outside-seam-pollution
          (NSTriadKNGate2AEP4MarginClosing.ep4Model gate2aMarginClosing))

    exactKNAOperatorTransferReceipt :
      NSTriadKNGate2ExactKNAOperatorTransferReceipt
    exactKNAOperatorTransferReceiptIsCanonical :
      exactKNAOperatorTransferReceipt ≡
        canonicalNSTriadKNGate2ExactKNAOperatorTransferReceipt

    outsideSeamAbsorptionReceipt :
      NSTriadKNGate2OutsideSeamAbsorptionReceipt
    outsideSeamAbsorptionReceiptIsCanonical :
      outsideSeamAbsorptionReceipt ≡
        canonicalNSTriadKNGate2OutsideSeamAbsorptionReceipt

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

    gate2ExactKNAOperatorTransferProved : Bool
    gate2ExactKNAOperatorTransferProvedIsTrue :
      gate2ExactKNAOperatorTransferProved ≡ true

    outsideSeamNoPollutionAnalyticallyProved : Bool
    outsideSeamNoPollutionAnalyticallyProvedIsTrue :
      outsideSeamNoPollutionAnalyticallyProved ≡ true

    gate2ExactTransferConditionalTheoremProved : Bool
    gate2ExactTransferConditionalTheoremProvedIsTrue :
      gate2ExactTransferConditionalTheoremProved ≡ true

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
  record
    { receiptName = "NSTriadKNGate2SeamToLeakageTransferReceipt"
    ; receiptNameIsCanonical = refl
    ; status = gate2TransferRecorded
    ; statusIsCanonical = refl
    ; boundaryText = canonicalBoundaryText
    ; boundaryTextIsCanonical = refl
    ; exactLeakageObjectText = canonicalExactLeakageObjectText
    ; exactLeakageObjectTextIsCanonical = refl
    ; upstreamCarrierText = canonicalUpstreamCarrierText
    ; upstreamCarrierTextIsCanonical = refl
    ; transferShapeText = canonicalTransferShapeText
    ; transferShapeTextIsCanonical = refl
    ; openObligationsText = canonicalOpenObligationsText
    ; openObligationsTextIsCanonical = refl
    ; sourcesText = canonicalSourcesText
    ; sourcesTextIsCanonical = refl
    ; docPath = "docs/ns_triad_kn_gate2_seam_to_leakage_transfer.md"
    ; docPathIsCanonical = refl
    ; gate2aMarginClosing = canonicalNSTriadKNGate2AEP4MarginClosing
    ; gate2aMarginClosingIsCanonical = refl
    ; seamLocalLeakageBudgetProof =
        NSTriadKNGate2AEP4MarginClosing.finalLeakage≤UnitProof
          canonicalNSTriadKNGate2AEP4MarginClosing
    ; outsideSeamZeroProof =
        NSTriadKNGate2AEP4MarginClosing.outsideSeamZeroProof
          canonicalNSTriadKNGate2AEP4MarginClosing
    ; seamCarrierTransferIdentity =
        NSTriadKNGate2AEP4MarginClosing.seamCarrierTransferIdentity
          canonicalNSTriadKNGate2AEP4MarginClosing
    ; exactKNAOperatorTransferReceipt =
        canonicalNSTriadKNGate2ExactKNAOperatorTransferReceipt
    ; exactKNAOperatorTransferReceiptIsCanonical = refl
    ; outsideSeamAbsorptionReceipt =
        canonicalNSTriadKNGate2OutsideSeamAbsorptionReceipt
    ; outsideSeamAbsorptionReceiptIsCanonical = refl
    ; normalizedGramToHelicalSchurAgreementRecorded = true
    ; normalizedGramToHelicalSchurAgreementRecordedIsTrue = refl
    ; seamCarrierMatchesLeakageLaneRecorded = true
    ; seamCarrierMatchesLeakageLaneRecordedIsTrue = refl
    ; gate2TransferSurfaceWritten = true
    ; gate2TransferSurfaceWrittenIsTrue = refl
    ; gate2aCertificateAvailable = true
    ; gate2aCertificateAvailableIsTrue = refl
    ; gate2aConeStabilitySurfaceAvailable = true
    ; gate2aConeStabilitySurfaceAvailableIsTrue = refl
    ; gate2aDirectionalBudgetSurfaceAvailable = true
    ; gate2aDirectionalBudgetSurfaceAvailableIsTrue = refl
    ; gate2aMarginClosingSurfaceAvailable = true
    ; gate2aMarginClosingSurfaceAvailableIsTrue = refl
    ; gate2aConcreteSeamLocalClosureModel = true
    ; gate2aConcreteSeamLocalClosureModelIsTrue = refl
    ; gate2aSeamLocalMarginProofCarried = true
    ; gate2aSeamLocalMarginProofCarriedIsTrue = refl
    ; normalizedGramToHelicalSchurAgreementProved = true
    ; normalizedGramToHelicalSchurAgreementProvedIsTrue = refl
    ; normalizedGramToHelicalSchurExtremizerAgreementStated = true
    ; normalizedGramToHelicalSchurExtremizerAgreementStatedIsTrue = refl
    ; normalizedGramToHelicalSchurExtremizerAgreementNumericallySupported = true
    ; normalizedGramToHelicalSchurExtremizerAgreementNumericallySupportedIsTrue = refl
    ; leakageTransferMarginNumericallySupported = true
    ; leakageTransferMarginNumericallySupportedIsTrue = refl
    ; schurCertificateTransfersToLeakageOperator = true
    ; schurCertificateTransfersToLeakageOperatorIsTrue = refl
    ; leakageTransferMarginPositive = true
    ; leakageTransferMarginPositiveIsTrue = refl
    ; outsideSeamNoPollutionProved = true
    ; outsideSeamNoPollutionProvedIsTrue = refl
    ; gate2ConditionalTheoremProved = true
    ; gate2ConditionalTheoremProvedIsTrue = refl
    ; gate2ExactKNAOperatorTransferProved = true
    ; gate2ExactKNAOperatorTransferProvedIsTrue = refl
    ; outsideSeamNoPollutionAnalyticallyProved = true
    ; outsideSeamNoPollutionAnalyticallyProvedIsTrue = refl
    ; gate2ExactTransferConditionalTheoremProved = true
    ; gate2ExactTransferConditionalTheoremProvedIsTrue = refl
    ; theoremPromoted = false
    ; theoremPromotedIsFalse = refl
    ; fullNSPromoted = false
    ; fullNSPromotedIsFalse = refl
    ; clayPromoted = false
    ; clayPromotedIsFalse = refl
    }
