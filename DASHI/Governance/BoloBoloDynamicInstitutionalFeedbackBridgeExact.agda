module DASHI.Governance.BoloBoloDynamicInstitutionalFeedbackBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.SocioEcologicalFeedbackExact as Feedback
import DASHI.Core.DeclaredRealisedInteractionTopologyExact as Runtime
import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact as HistoryEcology
import DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact as Polycentric
import DASHI.Governance.BoloBoloComparatorInstitutionalVersioningExact as Versioning

------------------------------------------------------------------------
-- DYNAMIC INSTITUTIONAL FEEDBACK CROSS-POLLINATION.
--
-- Source / attribution boundary:
--
-- * Ostrom's commons work motivates endogenous institutional response and, for
--   larger common-pool systems, governance organised in nested layers.
-- * Baldwin et al. (2024) independently synthesize empirical polycentric-
--   governance evidence and propose a Context -> Operations -> Outcomes ->
--   Feedbacks framing for long-run change.
-- * The exact finite non-factorability / realised-topology / history-sensitive
--   / adaptive-model-loop results reused below are DASHI results. They are not
--   attributed to Ostrom, Baldwin et al., p.m., Occupy participants, or the
--   comparator institutions.
--
-- Research consequence for bolo'bolo:
-- a one-shot inequality comparing removed global coupling against federation
-- overhead is only a snapshot unless actor adaptation, realised interaction
-- topology, institutional evolution and evidence-triggered model revision are
-- audited longitudinally.
------------------------------------------------------------------------

record DynamicInstitutionalFeedbackBridge : Set where
  constructor dynamicInstitutionalFeedbackBridge
  field
    socioEcologicalFeedbackBoundary : Feedback.SocioEcologicalFeedbackBoundary
    declaredRealisedTopologyBoundary : Runtime.DeclaredRealisedInteractionBoundary
    historyChoiceBoundary : HistoryChoice.HistoryConditionedChoiceBoundary
    adaptiveConsumerLoopBoundary : Adaptive.AdaptiveConsumerLoopBoundary
    historyEcologyOptionConeBoundary : HistoryEcology.HistoryEcologyOptionConeBoundary
    polycentricEvidenceSynthesis : Polycentric.PolycentricEvidenceSynthesis
    comparatorVersioningBoundary : Versioning.ComparatorVersioningBoundary

open DynamicInstitutionalFeedbackBridge public

canonicalDynamicInstitutionalFeedbackBridge : DynamicInstitutionalFeedbackBridge
canonicalDynamicInstitutionalFeedbackBridge = record
  { socioEcologicalFeedbackBoundary = Feedback.canonicalSocioEcologicalFeedbackBoundary
  ; declaredRealisedTopologyBoundary = Runtime.canonicalDeclaredRealisedInteractionBoundary
  ; historyChoiceBoundary = HistoryChoice.canonicalHistoryConditionedChoiceBoundary
  ; adaptiveConsumerLoopBoundary = Adaptive.canonicalAdaptiveConsumerLoopBoundary
  ; historyEcologyOptionConeBoundary = HistoryEcology.canonicalHistoryEcologyOptionConeBoundary
  ; polycentricEvidenceSynthesis = Polycentric.canonicalPolycentricEvidenceSynthesis
  ; comparatorVersioningBoundary = Versioning.canonicalComparatorVersioningBoundary
  }

record DynamicBoloEvaluationObligations : Set where
  constructor dynamicBoloEvaluationObligations
  field
    repeatedLongitudinalMeasurementRequired : Bool
    realisedInteractionTopologyAuditRequired : Bool
    actorAdaptationAuditRequired : Bool
    institutionalVersionWitnessRequired : Bool
    evidenceTriggeredModelRevisionRequired : Bool
    dependencyAffectedCertificatesMustBeReconsidered : Bool
    feedbackCanChangeFutureCoordinationSurface : Bool
    staticCostSnapshotAlonePaysLongRunPerformance : Bool
    declaredNestedArchitectureDeterminesRealisedCoordination : Bool
    samePresentSnapshotDeterminesFutureInstitutionalPath : Bool
    oldModelCertificateSurvivesContraryEvidenceAutomatically : Bool
    institutionalEvolutionAutomaticallyMeansImprovement : Bool
    crossContextDynamicTransportStillRequiresJustification : Bool

open DynamicBoloEvaluationObligations public

canonicalDynamicBoloEvaluationObligations : DynamicBoloEvaluationObligations
canonicalDynamicBoloEvaluationObligations =
  dynamicBoloEvaluationObligations
    true true true true true true true
    false false false false false true

------------------------------------------------------------------------
-- Exact repo witnesses carried into the governance interpretation.
------------------------------------------------------------------------

staticPlanScoreCanFailToDetermineReactiveOutcome :
  Feedback.staticScore Feedback.cooperativeWorld
  ≡ Feedback.staticScore Feedback.resistantWorld
staticPlanScoreCanFailToDetermineReactiveOutcome =
  Feedback.staticScoreCollision

sameDeclaredArchitectureCanHaveDifferentRealisedTopology :
  Runtime.declared Runtime.nominalDeployment
  ≡ Runtime.declared Runtime.emergentProtocolDeployment
sameDeclaredArchitectureCanHaveDifferentRealisedTopology =
  Runtime.sameDeclaredComputation

sameEcologyCanStillHaveHistoryConditionedOptionContraction :
  HistoryEcology.ecology HistoryEcology.regulatedSupportive
  ≡ HistoryEcology.ecology HistoryEcology.mobilisedSupportive
sameEcologyCanStillHaveHistoryConditionedOptionContraction =
  HistoryEcology.sameSupportiveEcology

record SourceAlignmentBoundary : Set where
  constructor sourceAlignmentBoundary
  field
    ostromNestedEnterprisesSupportsNestedGovernanceMotif : Bool
    baldwinCOOFFeedbackSupportsDynamicEvaluationMotif : Bool
    ostromOrBaldwinAuthoredDASHINonfactorabilityTheorems : Bool
    pMAuthoredDynamicFeedbackBridge : Bool
    comparatorEvolutionIsEvidenceOfBoloOptimality : Bool
    crossPollinationRetainsAttributionSeparation : Bool

open SourceAlignmentBoundary public

canonicalSourceAlignmentBoundary : SourceAlignmentBoundary
canonicalSourceAlignmentBoundary =
  sourceAlignmentBoundary true true false false false true

canonicalDynamicInstitutionalFeedbackReceipt : GenericReceipt.GenericReceipt
canonicalDynamicInstitutionalFeedbackReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo dynamic institutional feedback cross-pollination"
    "DASHI.Governance.BoloBoloDynamicInstitutionalFeedbackBridgeExact"
    "canonicalDynamicInstitutionalFeedbackBridge / canonicalDynamicBoloEvaluationObligations / canonicalSourceAlignmentBoundary"
    "reuses existing DASHI socio-ecological feedback, declared-versus-realised topology, history-conditioned choice/option-cone, adaptive evidence/model-reopening and comparator-versioning machinery to upgrade the bolo counterfactual from a static snapshot to a longitudinal adaptive-governance obligation, while aligning only the nested-governance and feedback motifs with independently sourced Ostrom and Baldwin et al. literature"
    "a favourable one-shot coordination inequality does not establish long-run performance: target evidence must audit actor adaptation, realised interaction topology, institutional version and feedback over time, and contrary evidence must reopen affected model certificates; the reused exact theorems remain DASHI results and are not attributed to p.m., Ostrom, Baldwin et al. or comparator actors"
    "agda -i . DASHI/Governance/BoloBoloDynamicInstitutionalFeedbackBridgeRegression.agda"
