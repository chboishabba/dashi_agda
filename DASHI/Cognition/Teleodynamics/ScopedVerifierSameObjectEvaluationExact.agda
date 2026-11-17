module DASHI.Cognition.Teleodynamics.ScopedVerifierSameObjectEvaluationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Cognition.Teleodynamics.ScopedVerifierEvaluationProtocolExact as Eval
import DASHI.Reasoning.RelationRepresentationExperimentProtocolExact as Protocol

------------------------------------------------------------------------
-- ELIGIBLE × SAME-OBJECT × HELD-OUT EVALUATION
--
-- Eligibility and empirical protocol are intentionally orthogonal obligations.
-- `Eval.EligibleEvaluationReceipt` pays the existing repo law
--
--   Admissible × ConsumerAdequate
--
-- for candidate and baseline in the SAME ConsumerMDLProblem.  The existing
-- relation/representation protocol separately pays matched pairing, four-axis
-- holdout scope, dynamic traces and target realization.
--
-- This owner only composes those obligations and adds literal equality receipts
-- for candidate/baseline case and intervention.  It defines neither a second
-- adequacy calculus nor a second experiment protocol.
------------------------------------------------------------------------

record SameObjectHeldOutEvaluation
    (problem : MDL.ConsumerMDLProblem) : Set₁ where
  constructor same-object-held-out-evaluation
  field
    eligibleEvaluation : Eval.EligibleEvaluationReceipt problem
    protocol : Protocol.RelationExperimentProtocol

    Case : Set
    candidateCase : Case
    baselineCase : Case
    sameCase : candidateCase ≡ baselineCase

    Intervention : Set
    candidateIntervention : Intervention
    baselineIntervention : Intervention
    sameIntervention : candidateIntervention ≡ baselineIntervention

    targetHoldoutPaid :
      Protocol.HeldOutScope.targetHeldOut (Protocol.heldOut protocol) ≡ true
    contextHoldoutPaid :
      Protocol.HeldOutScope.contextHeldOut (Protocol.heldOut protocol) ≡ true
    modelHoldoutPaid :
      Protocol.HeldOutScope.modelHeldOut (Protocol.heldOut protocol) ≡ true
    checkpointHoldoutPaid :
      Protocol.HeldOutScope.temporalCheckpointHeldOut
        (Protocol.heldOut protocol) ≡ true
    matchedPairingPaid : Protocol.matchedPairingDeclared protocol ≡ true
    dynamicTracePaid : Protocol.dynamicTraceRequired protocol ≡ true
    targetRealizationPaid : Protocol.targetRealizationRequired protocol ≡ true

    sameCaseReference : String
    sameInterventionReference : String
    evaluationProtocolReference : String

open SameObjectHeldOutEvaluation public

eligibleReceipt :
  ∀ {problem} →
  SameObjectHeldOutEvaluation problem →
  Eval.EligibleEvaluationReceipt problem
eligibleReceipt = eligibleEvaluation

candidateAdmissibilityPaid :
  ∀ {problem} →
  (receipt : SameObjectHeldOutEvaluation problem) →
  MDL.Admissible problem
    (Eval.candidateModel (eligibleEvaluation receipt))
candidateAdmissibilityPaid receipt =
  Eval.candidateAdmissibilityPaid (eligibleEvaluation receipt)

candidateConsumerAdequacyPaid :
  ∀ {problem} →
  (receipt : SameObjectHeldOutEvaluation problem) →
  MDL.ConsumerAdequate problem
    (Eval.candidateModel (eligibleEvaluation receipt))
candidateConsumerAdequacyPaid receipt =
  Eval.candidateConsumerAdequacyPaid (eligibleEvaluation receipt)

baselineAdmissibilityPaid :
  ∀ {problem} →
  (receipt : SameObjectHeldOutEvaluation problem) →
  MDL.Admissible problem
    (Eval.baselineModel (eligibleEvaluation receipt))
baselineAdmissibilityPaid receipt =
  Eval.baselineAdmissibilityPaid (eligibleEvaluation receipt)

baselineConsumerAdequacyPaid :
  ∀ {problem} →
  (receipt : SameObjectHeldOutEvaluation problem) →
  MDL.ConsumerAdequate problem
    (Eval.baselineModel (eligibleEvaluation receipt))
baselineConsumerAdequacyPaid receipt =
  Eval.baselineConsumerAdequacyPaid (eligibleEvaluation receipt)

record SameObjectEvaluationBoundary : Set where
  constructor same-object-evaluation-boundary
  field
    eligibilityRequiredBeforeEmpiricalRanking : Bool
    eligibilityAloneImpliesMatchedHeldOutExperiment : Bool
    sameCandidateBaselineCaseRequired : Bool
    sameCandidateBaselineInterventionRequired : Bool
    completeHeldOutAxisCoverageRequired : Bool
    matchedPairingRequired : Bool
    dynamicTraceRequired : Bool
    targetRealizationRequired : Bool
    consumerAdequacyImpliesWorldCompleteness : Bool
    matchedHeldOutFitImpliesMechanism : Bool
    equalScalarScoreImpliesTheoryIdentity : Bool

canonicalSameObjectEvaluationBoundary : SameObjectEvaluationBoundary
canonicalSameObjectEvaluationBoundary =
  same-object-evaluation-boundary
    true false true true true true true true false false false
