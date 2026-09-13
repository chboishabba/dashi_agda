module DASHI.Wikimedia.SensibLawZelphHFSelectorResultPaymentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact as DAG
import DASHI.Wikimedia.SensibLawStatementBundleDiagnosisProofSearchExact as Search
import DASHI.Wikimedia.SensibLawZelphHFPrerequisiteBridgeExact as Zelph

------------------------------------------------------------------------
-- ZELPH/HF SELECTOR RESULT -> VERIFIED PREREQUISITE DECISION
--
-- Mirrors the SensibLaw execution discipline:
--   sl.zelph.execution_receipt.v0_1 distinguishes execution outcome;
--   closure executors decode candidate proposals only;
--   canonical digests/lineage identify the bounded result;
--   the owning consumer still verifies whether that result pays its obligation.
------------------------------------------------------------------------

data SelectorExecutionOutcome : Set where
  executedWithOutput
  executedNoMatch
  failedRequiredOutputContract
  engineUnavailable
  engineFailed
  : SelectorExecutionOutcome

data ResultSignal : Set where
  supportsCurrentObligation
  insufficientForCurrentObligation
  conflictingBoundedEvidence
  changedContradictoryEvidence
  : ResultSignal

record ContentAddressReceipt : Set where
  constructor content-address-receipt
  field
    digestAlgorithm : String
    inputDigest : String
    outputDigest : String
    canonicalResultRef : String
    digestReference : String
open ContentAddressReceipt public

record SelectorLineageReceipt : Set where
  constructor selector-lineage-receipt
  field
    sourceSystem : String
    manifestReference : String
    inputRevision : String
    backendReference : String
    selectorReference : String
    upstreamArtifactReferences : List String
    lineageReference : String
open SelectorLineageReceipt public

record BoundedSelectorResult : Set where
  constructor bounded-selector-result
  field
    selector : Zelph.BoundedSelectorRequest
    executionOutcome : SelectorExecutionOutcome
    signal : ResultSignal
    contentAddress : ContentAddressReceipt
    lineage : SelectorLineageReceipt
    coverageComplete : Bool
    requiredOutputSatisfied : Bool
    resultReference : String
open BoundedSelectorResult public

resultObligation : BoundedSelectorResult → DAG.BundleObligation
resultObligation result = Zelph.prerequisite (selector result)

------------------------------------------------------------------------
-- An execution result is only a payment candidate. Actual payment requires a
-- separate consumer verification receipt for the same result/obligation.
------------------------------------------------------------------------

record PrerequisitePaymentCandidate (result : BoundedSelectorResult) : Set where
  constructor prerequisite-payment-candidate
  field
    targetObligation : DAG.BundleObligation
    targetExact : targetObligation ≡ resultObligation result
    candidateReference : String
    consumerVerificationStillRequired : Bool
    consumerVerificationStillRequiredIsTrue :
      consumerVerificationStillRequired ≡ true
open PrerequisitePaymentCandidate public

record VerifiedPrerequisitePayment (result : BoundedSelectorResult) : Set where
  constructor verified-prerequisite-payment
  field
    candidate : PrerequisitePaymentCandidate result
    executionWasWithOutput : executionOutcome result ≡ executedWithOutput
    signalSupportsTarget : signal result ≡ supportsCurrentObligation
    coverageWasComplete : coverageComplete result ≡ true
    requiredOutputWasSatisfied : requiredOutputSatisfied result ≡ true
    consumerVerificationReference : String
    sameResultReference : String
open VerifiedPrerequisitePayment public

------------------------------------------------------------------------
-- Result-sensitive graph feedback. Pay is proof-relevant; the other outcomes
-- preserve/revise the live diagnosis fibre without inventing negative truth.
------------------------------------------------------------------------

data SelectorResultDecision (result : BoundedSelectorResult) : Set where
  payPrerequisite :
    VerifiedPrerequisitePayment result → SelectorResultDecision result
  keepOpen :
    String → SelectorResultDecision result
  splitDiagnosis :
    List Search.BundleDiagnosis → String → SelectorResultDecision result
  reactivateDiagnosis :
    Search.BundleDiagnosis → String → String → SelectorResultDecision result

------------------------------------------------------------------------
-- Nat population / handoff calibration.  53 and 188 are bounded review
-- tranches, not the population. The sandbox-derived Cohort A population is
-- 37,665, with additional explicitly counted C/D/E-style populations.
------------------------------------------------------------------------

record NatPopulationHandoff : Set where
  constructor nat-population-handoff
  field
    businessFamilyPopulation : Nat
    missingInstanceOfPopulation : Nat
    unreconciledInstanceOfPopulation : Nat
    boundedMainlineComplete : Bool
    widerProofLaneComplete : Bool
    widerOnlineLaneHeld : Bool
    checkedSafePostEditVerifiedOnBoundedRows : Bool
    splitVerificationSingleAndBatch : Bool
    handoffReference : String
open NatPopulationHandoff public

natPopulationHandoff : NatPopulationHandoff
natPopulationHandoff =
  nat-population-handoff
    37665
    1395
    142
    true
    true
    true
    true
    true
    "SensibLaw Nat ontology-group handoff: bounded mainline/proof complete; wider online held; split verification active"

natBusinessPopulationIs37665 : businessFamilyPopulation natPopulationHandoff ≡ 37665
natBusinessPopulationIs37665 = refl

------------------------------------------------------------------------
-- Exact result fixtures for the four feedback branches.
------------------------------------------------------------------------

natSourceLineage : SelectorLineageReceipt
natSourceLineage =
  selector-lineage-receipt
    "SensibLaw/Wikidata/Zelph-HF"
    "zelph-hf-layout/v2"
    "Nat P5991/P14143 revision-locked bounded selector input"
    "zelph-closure-executor:v0_1"
    "sel:nat:q10403939:p5991-p14143:source-support"
    ("Nat cohort/review packet" ∷ "bounded WD selector result" ∷ [])
    "append-only selector-result lineage; later receipts do not rewrite earlier packet state"

natSourceDigest : ContentAddressReceipt
natSourceDigest =
  content-address-receipt
    "sha256"
    "sha256:nat-source-selector-input"
    "sha256:nat-source-selector-output"
    "selector-result:sha256:nat-source-selector-output"
    "canonical content address placeholder carried as receipt identity, not source authority"

natSupportiveResult : BoundedSelectorResult
natSupportiveResult =
  bounded-selector-result
    Zelph.natClimateSourceSelector
    executedWithOutput
    supportsCurrentObligation
    natSourceDigest
    natSourceLineage
    true
    true
    "bounded source-support result with complete required-output contract"

natSupportCandidate : PrerequisitePaymentCandidate natSupportiveResult
natSupportCandidate =
  prerequisite-payment-candidate
    DAG.sourceSupport
    refl
    "source-support payment candidate from bounded selector output"
    true refl

natSupportVerified : VerifiedPrerequisitePayment natSupportiveResult
natSupportVerified =
  verified-prerequisite-payment
    natSupportCandidate
    refl refl refl refl
    "owning Nat consumer verifies exact source-support obligation"
    "verification binds the same content-addressed bounded result"

natPayDecision : SelectorResultDecision natSupportiveResult
natPayDecision = payPrerequisite natSupportVerified

natNoMatchResult : BoundedSelectorResult
natNoMatchResult =
  bounded-selector-result
    Zelph.natClimateSourceSelector
    executedNoMatch
    insufficientForCurrentObligation
    natSourceDigest
    natSourceLineage
    false
    true
    "executed no-match; zero result is not negative evidence"

natKeepOpenDecision : SelectorResultDecision natNoMatchResult
natKeepOpenDecision =
  keepOpen "selector completed but did not provide sufficient evidence to pay source support"

natConflictResult : BoundedSelectorResult
natConflictResult =
  bounded-selector-result
    Zelph.natClimateSourceSelector
    executedWithOutput
    conflictingBoundedEvidence
    natSourceDigest
    natSourceLineage
    true
    true
    "bounded result exposes incompatible source/provenance interpretations"

natSplitDecision : SelectorResultDecision natConflictResult
natSplitDecision =
  splitDiagnosis
    (Search.referenceDrift ∷ Search.provenanceGap ∷ [])
    "preserve both reference-drift and provenance-gap diagnoses for follow-up discrimination"

natChangedContradictionResult : BoundedSelectorResult
natChangedContradictionResult =
  bounded-selector-result
    Zelph.natClimateSourceSelector
    executedWithOutput
    changedContradictoryEvidence
    natSourceDigest
    natSourceLineage
    true
    true
    "new revision-locked bounded evidence contradicts an assumption used by a previously closed diagnosis"

natReactivateDecision : SelectorResultDecision natChangedContradictionResult
natReactivateDecision =
  reactivateDiagnosis
    Search.referenceDrift
    "reactivate only the dependency-local diagnosis whose supporting source/reference relation changed"
    "historical closure receipt remains in append-only lineage and is not rewritten"

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data ExecutedWithOutputAutomaticallyPaysPrerequisite : Set where
data ContentDigestCreatesAuthority : Set where
data NoMatchMeansNegativeEvidence : Set where
data SplitDiagnosisMeansMigrationFailure : Set where
data ReactivationRewritesHistoricalClosure : Set where
data BoundedPaymentMeansFullPopulationSafe : Set where

executedOutputDoesNotAutomaticallyPay :
  ExecutedWithOutputAutomaticallyPaysPrerequisite → ⊥
executedOutputDoesNotAutomaticallyPay ()

contentDigestDoesNotCreateAuthority : ContentDigestCreatesAuthority → ⊥
contentDigestDoesNotCreateAuthority ()

noMatchDoesNotMeanNegativeEvidence : NoMatchMeansNegativeEvidence → ⊥
noMatchDoesNotMeanNegativeEvidence ()

splitDiagnosisDoesNotMeanMigrationFailure : SplitDiagnosisMeansMigrationFailure → ⊥
splitDiagnosisDoesNotMeanMigrationFailure ()

reactivationDoesNotRewriteHistoricalClosure :
  ReactivationRewritesHistoricalClosure → ⊥
reactivationDoesNotRewriteHistoricalClosure ()

boundedPaymentDoesNotMakeFullPopulationSafe : BoundedPaymentMeansFullPopulationSafe → ⊥
boundedPaymentDoesNotMakeFullPopulationSafe ()

record SelectorResultPaymentBoundary : Set where
  constructor selector-result-payment-boundary
  field
    executionOutputIsOnlyPaymentCandidate : Bool
    verifiedPaymentRequiresSameResultConsumerReceipt : Bool
    noMatchIsNegativeEvidence : Bool
    splitIsUsefulReviewOutcome : Bool
    reactivationPreservesHistoricalLineage : Bool
    contentAddressCreatesAuthority : Bool
    boundedRowPaymentPromotesWholeNatPopulation : Bool

canonicalSelectorResultPaymentBoundary : SelectorResultPaymentBoundary
canonicalSelectorResultPaymentBoundary =
  selector-result-payment-boundary true true false true true false false
