module DASHI.Programmes.TestHarnessFamilyReceiptExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- dashitest is a heterogeneous laboratory, not one experiment.  Its outputs
-- therefore need experiment-family indexing before they can enter the formal
-- prediction/evidence spine.
------------------------------------------------------------------------

data TestHarnessFamily : Set where
  trading : TestHarnessFamily
  epistemicCA : TestHarnessFamily
  compression : TestHarnessFamily
  treeDiffusion : TestHarnessFamily
  quotientLearning : TestHarnessFamily
  reactionDiffusion : TestHarnessFamily
  valuationPrimes : TestHarnessFamily
  backendParity : TestHarnessFamily
  sparseLearning : TestHarnessFamily
  ternaryArithmetic : TestHarnessFamily
  otherDeclaredFamily : TestHarnessFamily

record TestHarnessArtifactReceipt : Set₁ where
  constructor test-harness-artifact-receipt
  field
    Family State Prediction Evidence Artifact : Set
    family : Family → TestHarnessFamily
    stateCompatible : Evidence → State → Set
    predictionReadout : State → Prediction
    artifactEvidence : Artifact → Evidence

    -- Provenance and criterion ownership are explicit because many dashitest
    -- scripts are exploratory/visual rather than theorem-facing.
    provenanceReceipt : Artifact → Set
    criterionDeclaredBeforeEvaluation : Artifact → Set

open TestHarnessArtifactReceipt public

record TestHarnessFamilyBoundary : Set where
  constructor test-harness-family-boundary
  field
    oneGlobalBenchmarkPassedBooleanIsSufficient : Bool
    oneGlobalBenchmarkPassedBooleanIsSufficientIsFalse :
      oneGlobalBenchmarkPassedBooleanIsSufficient ≡ false

    diagnosticPlotIsOperationalEvidenceByDefault : Bool
    diagnosticPlotIsOperationalEvidenceByDefaultIsFalse :
      diagnosticPlotIsOperationalEvidenceByDefault ≡ false

    familyIndexedTypedReceiptCanEnterPredictionEnvelope : Bool
    familyIndexedTypedReceiptCanEnterPredictionEnvelopeIsTrue :
      familyIndexedTypedReceiptCanEnterPredictionEnvelope ≡ true

    postHocAcceptanceCriterionIsIndependentValidation : Bool
    postHocAcceptanceCriterionIsIndependentValidationIsFalse :
      postHocAcceptanceCriterionIsIndependentValidation ≡ false

canonicalTestHarnessFamilyBoundary : TestHarnessFamilyBoundary
canonicalTestHarnessFamilyBoundary =
  test-harness-family-boundary
    false refl
    false refl
    true refl
    false refl
