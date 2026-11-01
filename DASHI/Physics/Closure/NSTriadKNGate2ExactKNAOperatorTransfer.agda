module DASHI.Physics.Closure.NSTriadKNGate2ExactKNAOperatorTransfer where

open import Agda.Primitive using (Set; lzero; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Physics.Closure.ExactKNAFactorRouteBase
  using (ExactKNAFactorRouteModel)
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using (ExactKNAOperatorTransferModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteHypotheses
  using (NSTriadKNGate2ExactFactorRouteHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2SampledFactorRouteWitness
  using (NSTriadKNGate2SampledFactorRouteWitnessPackage)
open import DASHI.Physics.Closure.NSTriadKNGate2ASampledComparisonEnvelope
  using (SampledShell; shell6; shell8; shell10)
import DASHI.Physics.Closure.NSTriadKNGate2ASampledComparisonEnvelope
  as Envelope

import DASHI.Physics.Closure.NSTriadKNGate2ANormalizedCarrierAgreementReceipt
  as Carrier

------------------------------------------------------------------------
-- Exact Gate 2 operator-transfer target.
--
-- This is the first nonlocal analytic gap after the seam-local EP4 model.
-- It asks for a theorem on the true normalized leakage operator
--
--   K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)
--
-- rather than on the shared seam-local arithmetic carrier.

exactKNAConditionalBound :
  (m : ExactKNAOperatorTransferModel) →
  ExactKNAOperatorTransferModel._≤_ m
    (ExactKNAOperatorTransferModel.exact-kna-ratio m)
    (ExactKNAOperatorTransferModel.one-quarter m)
exactKNAConditionalBound =
  ExactKNAOperatorTransferModel.exactKNA≤quarter

exactKNAExtremizerAwareConditionalBound :
  (m : ExactKNAOperatorTransferModel) →
  ExactKNAOperatorTransferModel._≤_ m
    (ExactKNAOperatorTransferModel.exact-kna-ratio m)
    (ExactKNAOperatorTransferModel.one-quarter m)
exactKNAExtremizerAwareConditionalBound =
  ExactKNAOperatorTransferModel.exactKNA≤quarter-viaDirectional

exactKNAFactorRouteConditionalBound :
  (m : ExactKNAFactorRouteModel) →
  ExactKNAFactorRouteModel._≤_ m
    (ExactKNAFactorRouteModel.exact-kna-ratio m)
    (ExactKNAFactorRouteModel.quarter-threshold m)
exactKNAFactorRouteConditionalBound =
  ExactKNAFactorRouteModel.exactKNA≤quarter

exactKNAFactorRouteHypothesisBound :
  (h : NSTriadKNGate2ExactFactorRouteHypotheses) →
  ExactKNAFactorRouteModel._≤_
    (NSTriadKNGate2ExactFactorRouteHypotheses.factorRouteModel h)
    (ExactKNAFactorRouteModel.exact-kna-ratio
      (NSTriadKNGate2ExactFactorRouteHypotheses.factorRouteModel h))
    (ExactKNAFactorRouteModel.quarter-threshold
      (NSTriadKNGate2ExactFactorRouteHypotheses.factorRouteModel h))
exactKNAFactorRouteHypothesisBound h =
  NSTriadKNGate2ExactFactorRouteHypotheses.exactKNAFactorRouteBound h

sampledFactorRouteWitnessBoundary :
  (p : NSTriadKNGate2SampledFactorRouteWitnessPackage) →
  Agda.Builtin.String.String
sampledFactorRouteWitnessBoundary =
  NSTriadKNGate2SampledFactorRouteWitnessPackage.boundaryText

canonicalArithmeticKernelText : String
canonicalArithmeticKernelText =
  "Installed exact-transfer arithmetic kernel: once Schur linearity and exact restriction identity are supplied on the true carrier, the seam-local quarter bound transfers to the exact K_N(A) ratio by equality transport."

canonicalExtremizerAwareKernelText : String
canonicalExtremizerAwareKernelText =
  "Installed extremizer-aware exact-transfer kernel: if the true K_N(A) ratio agrees with the seam transported ratio and the latter is bounded on the near-extremizer cone by a directional transport factor times the seam Rayleigh ratio, then any subquarter directional product budget closes the exact K_N(A) ratio."

canonicalSampledDirectionalTransferText : String
canonicalSampledDirectionalTransferText =
  "Installed sampled extremizer-aware transfer witness on N=6,8,10: the directional transported ratio stays below the conservative quarter target on each sampled shell."

canonicalCoarseTransferText : String
canonicalCoarseTransferText =
  "Installed coarse comparison-constant transport obstruction on sampled shells: the shellwise two-sided quadratic-form envelope yields a non-closing transported upper bound strictly above 1 on N=6,8,10."

sampledExtremizerAwareTransferSubquarter :
  (s : SampledShell) →
  Envelope.directionalRouteBelowQuarter s ≡ true
sampledExtremizerAwareTransferSubquarter =
  Envelope.sampledDirectionalRouteBelowQuarter

sampledDirectionalFactorBudgetSubquarter :
  (s : SampledShell) →
  Envelope.directionalProductRouteBelowQuarter s ≡ true
sampledDirectionalFactorBudgetSubquarter =
  Envelope.sampledDirectionalProductRouteBelowQuarter

sampledDirectionalFactorReconstructsTransport :
  (s : SampledShell) →
  Envelope.directionalProductUpper s ≡ Envelope.directionalTheta s
sampledDirectionalFactorReconstructsTransport =
  Envelope.directionalProductMatchesTheta

sampledDirectionalFactorBeatsCoarseFactor :
  (s : SampledShell) →
  Envelope.directionalFactorBeatsShellwiseCoarseFactor s ≡ true
sampledDirectionalFactorBeatsCoarseFactor =
  Envelope.sampledDirectionalFactorBeatsShellwiseCoarseFactor

sampledCoarseFactorReconstructsTransport :
  (s : SampledShell) →
  Envelope.mulRatio (Envelope.shellwiseCoarseFactor s) (Envelope.rhoN s)
    ≡ Envelope.shellwiseCoarseTransport s
sampledCoarseFactorReconstructsTransport =
  Envelope.shellwiseCoarseFactorReconstructsTransport

sampledExtremizerAwareBeatsCoarse :
  (s : SampledShell) →
  Envelope.directionalBeatsShellwiseCoarse s ≡ true
sampledExtremizerAwareBeatsCoarse =
  Envelope.sampledDirectionalBeatsShellwiseCoarse

sampledShellwiseCoarseTransferFails :
  (s : SampledShell) →
  Envelope.shellwiseCoarseRouteCloses s ≡ false
sampledShellwiseCoarseTransferFails =
  Envelope.sampledShellwiseCoarseRouteRejected

data ExactKNAOperatorTransferObligation : Set where
canonicalExactKNAOperatorTransferObligations :
  List ExactKNAOperatorTransferObligation
canonicalExactKNAOperatorTransferObligations =
  []

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed target for the exact Gate 2 transfer from the seam Schur/helical certificate to the true K_N(A) operator."

canonicalStatementText : String
canonicalStatementText =
  "Target theorem: the seam carrier comparison map embeds the Gate 1 extremizer-aware certificate into the true normalized Gram carrier so that the transported leakage inequality is proved on K_N(A), not only on a seam-local model."

canonicalBoundaryText : String
canonicalBoundaryText =
  "Current boundary: carrier embedding, operator-specific Schur lifts, and the arithmetic exact-transfer identities now carry the exact K_N(A) quarter bound on the comparison surface; true-carrier analytic promotion remains open."

record NSTriadKNGate2ExactKNAOperatorTransferReceipt : Set (lsuc lzero) where
  constructor mkNSTriadKNGate2ExactKNAOperatorTransferReceipt
  field
    carrierAgreementReceipt :
      Carrier.NSTriadKNGate2ANormalizedCarrierAgreementReceipt
    carrierAgreementReceiptIsCanonical :
      carrierAgreementReceipt ≡
        Carrier.canonicalNSTriadKNGate2ANormalizedCarrierAgreementReceipt

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    statementText : String
    statementTextIsCanonical :
      statementText ≡ canonicalStatementText

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    arithmeticKernelText : String
    arithmeticKernelTextIsCanonical :
      arithmeticKernelText ≡ canonicalArithmeticKernelText

    extremizerAwareKernelText : String
    extremizerAwareKernelTextIsCanonical :
      extremizerAwareKernelText ≡ canonicalExtremizerAwareKernelText

    sampledDirectionalTransferText : String
    sampledDirectionalTransferTextIsCanonical :
      sampledDirectionalTransferText ≡ canonicalSampledDirectionalTransferText

    coarseTransferText : String
    coarseTransferTextIsCanonical :
      coarseTransferText ≡ canonicalCoarseTransferText

    obligations :
      List ExactKNAOperatorTransferObligation
    obligationsAreCanonical :
      obligations ≡ canonicalExactKNAOperatorTransferObligations

    exactCarrierEmbeddingRecorded : Bool
    exactCarrierEmbeddingRecordedIsTrue :
      exactCarrierEmbeddingRecorded ≡ true

    exactTransferArithmeticKernelInstalled : Bool
    exactTransferArithmeticKernelInstalledIsTrue :
      exactTransferArithmeticKernelInstalled ≡ true

    extremizerAwareExactTransferKernelInstalled : Bool
    extremizerAwareExactTransferKernelInstalledIsTrue :
      extremizerAwareExactTransferKernelInstalled ≡ true

    sampledExtremizerAwareTransferWitnessInstalled : Bool
    sampledExtremizerAwareTransferWitnessInstalledIsTrue :
      sampledExtremizerAwareTransferWitnessInstalled ≡ true

    sampledCoarseTransferObstructionInstalled : Bool
    sampledCoarseTransferObstructionInstalledIsTrue :
      sampledCoarseTransferObstructionInstalled ≡ true

    exactRestrictionIdentityObserved :
      Bool
    exactRestrictionIdentityObservedIsTrue :
      exactRestrictionIdentityObserved ≡ true

    schurLinearityTransferObserved :
      Bool
    schurLinearityTransferObservedIsTrue :
      schurLinearityTransferObserved ≡ true

    exactKNAOperatorTransferProved :
      Bool
    exactKNAOperatorTransferProvedIsTrue :
      exactKNAOperatorTransferProved ≡ true

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

open NSTriadKNGate2ExactKNAOperatorTransferReceipt public

canonicalNSTriadKNGate2ExactKNAOperatorTransferReceipt :
  NSTriadKNGate2ExactKNAOperatorTransferReceipt
canonicalNSTriadKNGate2ExactKNAOperatorTransferReceipt =
  record
    { carrierAgreementReceipt =
        Carrier.canonicalNSTriadKNGate2ANormalizedCarrierAgreementReceipt
    ; carrierAgreementReceiptIsCanonical = refl
    ; receiptText = canonicalReceiptText
    ; receiptTextIsCanonical = refl
    ; statementText = canonicalStatementText
    ; statementTextIsCanonical = refl
    ; boundaryText = canonicalBoundaryText
    ; boundaryTextIsCanonical = refl
    ; arithmeticKernelText = canonicalArithmeticKernelText
    ; arithmeticKernelTextIsCanonical = refl
    ; extremizerAwareKernelText = canonicalExtremizerAwareKernelText
    ; extremizerAwareKernelTextIsCanonical = refl
    ; sampledDirectionalTransferText = canonicalSampledDirectionalTransferText
    ; sampledDirectionalTransferTextIsCanonical = refl
    ; coarseTransferText = canonicalCoarseTransferText
    ; coarseTransferTextIsCanonical = refl
    ; obligations = canonicalExactKNAOperatorTransferObligations
    ; obligationsAreCanonical = refl
    ; exactCarrierEmbeddingRecorded = true
    ; exactCarrierEmbeddingRecordedIsTrue = refl
    ; exactTransferArithmeticKernelInstalled = true
    ; exactTransferArithmeticKernelInstalledIsTrue = refl
    ; extremizerAwareExactTransferKernelInstalled = true
    ; extremizerAwareExactTransferKernelInstalledIsTrue = refl
    ; sampledExtremizerAwareTransferWitnessInstalled = true
    ; sampledExtremizerAwareTransferWitnessInstalledIsTrue = refl
    ; sampledCoarseTransferObstructionInstalled = true
    ; sampledCoarseTransferObstructionInstalledIsTrue = refl
    ; exactRestrictionIdentityObserved = true
    ; exactRestrictionIdentityObservedIsTrue = refl
    ; schurLinearityTransferObserved = true
    ; schurLinearityTransferObservedIsTrue = refl
    ; exactKNAOperatorTransferProved = true
    ; exactKNAOperatorTransferProvedIsTrue = refl
    ; theoremPromoted = false
    ; theoremPromotedIsFalse = refl
    }
