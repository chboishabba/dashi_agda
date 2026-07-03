module DASHI.Physics.Closure.NSTriadKNGate2ExactKNAOperatorTransfer where

open import Agda.Primitive using (Setω)
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
  exactCarrierEmbeddingOpen :
    ExactKNAOperatorTransferObligation
  exactRestrictionIdentityOpen :
    ExactKNAOperatorTransferObligation
  schurLinearityTransferOpen :
    ExactKNAOperatorTransferObligation
  exactNormalizedLeakageTransferOpen :
    ExactKNAOperatorTransferObligation

canonicalExactKNAOperatorTransferObligations :
  List ExactKNAOperatorTransferObligation
canonicalExactKNAOperatorTransferObligations =
  exactCarrierEmbeddingOpen
  ∷ exactRestrictionIdentityOpen
  ∷ schurLinearityTransferOpen
  ∷ exactNormalizedLeakageTransferOpen
  ∷ []

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed target for the exact Gate 2 transfer from the seam Schur/helical certificate to the true K_N(A) operator."

canonicalStatementText : String
canonicalStatementText =
  "Target theorem: the seam carrier comparison map embeds the Gate 1 extremizer-aware certificate into the true normalized Gram carrier so that the transported leakage inequality is proved on K_N(A), not only on a seam-local model."

canonicalBoundaryText : String
canonicalBoundaryText =
  "Current boundary: operator-specific Schur lifts are recorded, two-sided comparison telemetry exists, but exact restriction identity, Schur linearity transfer, and exact K_N(A) transport remain open."

record NSTriadKNGate2ExactKNAOperatorTransferReceipt : Setω where
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
    exactRestrictionIdentityObservedIsFalse :
      exactRestrictionIdentityObserved ≡ false

    schurLinearityTransferObserved :
      Bool
    schurLinearityTransferObservedIsFalse :
      schurLinearityTransferObserved ≡ false

    exactKNAOperatorTransferProved :
      Bool
    exactKNAOperatorTransferProvedIsFalse :
      exactKNAOperatorTransferProved ≡ false

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

open NSTriadKNGate2ExactKNAOperatorTransferReceipt public

canonicalNSTriadKNGate2ExactKNAOperatorTransferReceipt :
  NSTriadKNGate2ExactKNAOperatorTransferReceipt
canonicalNSTriadKNGate2ExactKNAOperatorTransferReceipt =
  mkNSTriadKNGate2ExactKNAOperatorTransferReceipt
    Carrier.canonicalNSTriadKNGate2ANormalizedCarrierAgreementReceipt
    refl
    canonicalReceiptText
    refl
    canonicalStatementText
    refl
    canonicalBoundaryText
    refl
    canonicalArithmeticKernelText
    refl
    canonicalExtremizerAwareKernelText
    refl
    canonicalSampledDirectionalTransferText
    refl
    canonicalCoarseTransferText
    refl
    canonicalExactKNAOperatorTransferObligations
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
    false
    refl
