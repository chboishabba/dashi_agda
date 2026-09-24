module DASHI.Education.DigitalESDTransformativePrincipleMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalInnovationESDTransformationExact as Transformation
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Principles
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence
import DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact as Primary
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Prior
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Scholarly

------------------------------------------------------------------------
-- DIGITAL-ESD TRANSFORMATIVE PRINCIPLE MATRIX
--
-- Corpus A supplies source-attributed digital-education principles.
-- The canonical transformation owner supplies enactment/scaling conditions.
-- Corpus B supplies sustainability/ESD constraints and contextual evidence.
-- The externality-incidence owner keeps contribution, benefit, burden, voice,
-- control, exit, lifecycle stage, time and material position distinct.
--
--   pedagogical principle support != scaling condition != sustainability evidence
--
-- A matrix row is therefore a candidate synthesis cell, not a new empirical
-- result and not a claim that the Alice/colleague papers contained the B-side
-- sustainability evidence or proved scalable implementation.
------------------------------------------------------------------------

data SustainabilityConstraint : Set where
  socialEquityAndInclusion : SustainabilityConstraint
  epistemicAgencyAndPublicGovernance : SustainabilityConstraint
  environmentalLifecycleAndCircularity : SustainabilityConstraint
  economicTCOAndProcurement : SustainabilityConstraint
  infrastructureOpennessAndInteroperability : SustainabilityConstraint
  institutionalDurabilityAndMonitoring : SustainabilityConstraint
  intergenerationalOptionPreservation : SustainabilityConstraint

constraintName : SustainabilityConstraint → String
constraintName socialEquityAndInclusion =
  "social equity, inclusion and distribution of benefits/burdens"
constraintName epistemicAgencyAndPublicGovernance =
  "epistemic agency, deliberative governance and public accountability"
constraintName environmentalLifecycleAndCircularity =
  "environmental lifecycle, service life, repair, reuse and circularity"
constraintName economicTCOAndProcurement =
  "total cost of ownership, procurement and long-horizon resource commitments"
constraintName infrastructureOpennessAndInteroperability =
  "openness, interoperability, portability, migration and exit"
constraintName institutionalDurabilityAndMonitoring =
  "institutional durability, monitoring, integration depth and longitudinal revision"
constraintName intergenerationalOptionPreservation =
  "preservation of future learner/institutional options under long-horizon consequences"

externalityIncidenceBoundary : Incidence.ExternalityIncidenceBoundary
externalityIncidenceBoundary = Incidence.canonicalExternalityIncidenceBoundary

record PrincipleConstraintRow : Set where
  constructor principle-constraint-row
  field
    pedagogicalPrinciple : Principles.TransferablePedagogicalPrinciple
    scalingConditions : List Transformation.ScalingCondition
    constraints : List SustainabilityConstraint
    sustainabilitySources : List Attr.AttributedSource
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    crossPollinationReading : String
    nonPromotionBoundary : String

open PrincipleConstraintRow public

situatedRelationalEngagementConstraintRow : PrincipleConstraintRow
situatedRelationalEngagementConstraintRow =
  principle-constraint-row
    Principles.situatedRelationalEngagement
    ( Transformation.scalablePedagogyCondition
    ∷ Transformation.institutionalPracticeCondition
    ∷ Transformation.professionalDevelopmentCondition
    ∷ [] )
    ( socialEquityAndInclusion
    ∷ institutionalDurabilityAndMonitoring
    ∷ [] )
    ( Primary.oecdDigitalEducationOutlook2026Source
    ∷ Primary.uneceFifthESDEvaluationSource
    ∷ Prior.publicDigitalLearningPlatformCharterSource
    ∷ Scholarly.gousetiPlatformisationSource
    ∷ [] )
    true refl
    "Situated relational engagement becomes a digital-ESD principle only when access, interaction and pedagogy are read together with educator capability, institutional practice, equity, inclusion, public-platform governance and the conditions that allow engagement to persist."
    "The Alice-side engagement synthesis does not itself establish equity, professional-development effectiveness or durability; the B-side sources do not validate the Alice corpus mechanisms in every sustainability context."

feedbackAsRevisableSignalConstraintRow : PrincipleConstraintRow
feedbackAsRevisableSignalConstraintRow =
  principle-constraint-row
    Principles.feedbackAsRevisableSignal
    ( Transformation.institutionalPracticeCondition
    ∷ Transformation.professionalDevelopmentCondition
    ∷ Transformation.policyCondition
    ∷ [] )
    ( epistemicAgencyAndPublicGovernance
    ∷ socialEquityAndInclusion
    ∷ institutionalDurabilityAndMonitoring
    ∷ [] )
    ( Primary.unescoAICommonGoodMinisterialSource
    ∷ Prior.publicDigitalLearningPlatformCharterSource
    ∷ Primary.oecdDigitalEducationOutlook2026Source
    ∷ Scholarly.gousetiPlatformisationSource
    ∷ [] )
    true refl
    "Feedback analytics and AI classifications can support sustainability-oriented adaptation only as contestable, human-reviewed signals embedded in educator capability, institutional routines, rights, public accountability and longitudinal monitoring."
    "Model output is not student meaning or policy authority. Governance sources do not prove classifier accuracy or pedagogical effect, and classifier feasibility does not pay governance or professional-development obligations."

constitutiveLearnerAgencyConstraintRow : PrincipleConstraintRow
constitutiveLearnerAgencyConstraintRow =
  principle-constraint-row
    Principles.constitutiveLearnerAgency
    ( Transformation.scalablePedagogyCondition
    ∷ Transformation.institutionalPracticeCondition
    ∷ Transformation.policyCondition
    ∷ [] )
    ( epistemicAgencyAndPublicGovernance
    ∷ socialEquityAndInclusion
    ∷ intergenerationalOptionPreservation
    ∷ [] )
    ( Primary.unescoAICommonGoodMinisterialSource
    ∷ Prior.fernandoTajanParticipatoryESDSource
    ∷ Prior.publicDigitalLearningPlatformCharterSource
    ∷ Scholarly.ardilaDigitalFuturesSource
    ∷ [] )
    true refl
    "Learners should be treated as situated contributors to questions, interpretation and design rather than merely recipients of sustainable-development content. Scaling that practice requires pedagogical, institutional and policy arrangements that keep participation consequential rather than symbolic."
    "Prior participatory or governance literature does not create constitutive authority for a new target population. Consultation, consent, co-design and representation remain distinct coordinates."

adaptiveSupportWithLocalChoiceConstraintRow : PrincipleConstraintRow
adaptiveSupportWithLocalChoiceConstraintRow =
  principle-constraint-row
    Principles.adaptiveSupportWithLocalChoice
    ( Transformation.scalablePedagogyCondition
    ∷ Transformation.institutionalPracticeCondition
    ∷ Transformation.professionalDevelopmentCondition
    ∷ [] )
    ( socialEquityAndInclusion
    ∷ institutionalDurabilityAndMonitoring
    ∷ economicTCOAndProcurement
    ∷ [] )
    ( Primary.oecdDigitalEducationOutlook2026Source
    ∷ Primary.uneceFifthESDEvaluationSource
    ∷ Primary.unescoAITCOBackgroundSource
    ∷ Scholarly.holstSDG47MonitoringSource
    ∷ [] )
    true refl
    "Support strategies should remain locally selectable and revisable while educators and institutions have the capability to enact them and account for uneven access, long-horizon integration and the full system cost of sustaining the chosen support infrastructure."
    "A support strategy valued in one student population is not a universal prescription; TCO, professional-development and monitoring coordinates specify additional obligations without proving local educational effectiveness."

pluralSituatedObserversConstraintRow : PrincipleConstraintRow
pluralSituatedObserversConstraintRow =
  principle-constraint-row
    Principles.pluralSituatedObservers
    ( Transformation.institutionalPracticeCondition
    ∷ Transformation.professionalDevelopmentCondition
    ∷ Transformation.policyCondition
    ∷ [] )
    ( socialEquityAndInclusion
    ∷ epistemicAgencyAndPublicGovernance
    ∷ environmentalLifecycleAndCircularity
    ∷ [] )
    ( Primary.unescoAICommonGoodMinisterialSource
    ∷ Scholarly.chughSustainabilityParadoxSource
    ∷ Prior.ituGlobalEwasteSource
    ∷ Scholarly.gousetiPlatformisationSource
    ∷ [] )
    true refl
    "A sustainability assessment should ask not only whether a digital intervention works, but whose observer surface is represented, who benefits, who bears surveillance/material/exclusion burdens, and which impacts remain outside the dominant institutional view. Institutions and educators need practices for holding those observer differences rather than flattening them."
    "Plural-observer analysis does not imply all perspectives are equivalent or that any single situated report proves lifecycle impact, institutional intent or population prevalence."

contextualCustodianshipConstraintRow : PrincipleConstraintRow
contextualCustodianshipConstraintRow =
  principle-constraint-row
    Principles.contextualCustodianship
    ( Transformation.institutionalPracticeCondition
    ∷ Transformation.professionalDevelopmentCondition
    ∷ Transformation.policyCondition
    ∷ [] )
    ( environmentalLifecycleAndCircularity
    ∷ economicTCOAndProcurement
    ∷ infrastructureOpennessAndInteroperability
    ∷ socialEquityAndInclusion
    ∷ [] )
    ( ICT.ituL1410LifecycleMethodSource
    ∷ ICT.ituL1023CircularityMethodSource
    ∷ Primary.unescoAITCOBackgroundSource
    ∷ Primary.unescoAIProcurementBackgroundSource
    ∷ Prior.publicDigitalLearningPlatformCharterSource
    ∷ Scholarly.chughSustainabilityParadoxSource
    ∷ [] )
    true refl
    "The ecology-of-data demand to map edges, affordances, effort and value flows expands into material and institutional custodianship: devices, networks, energy, repair, procurement, portability, vendor dependence and externality incidence become educational concerns that require institutional capability and policy support."
    "This is a cross-domain synthesis. ITU methods and governance sources define observables and obligations but do not supply a same-object lifecycle inventory, circularity score, procurement result, burden allocation or sustainability verdict for a digital-education deployment."

iterativeEvidenceReturnAndRechartingConstraintRow : PrincipleConstraintRow
iterativeEvidenceReturnAndRechartingConstraintRow =
  principle-constraint-row
    Principles.iterativeEvidenceReturnAndRecharting
    ( Transformation.institutionalPracticeCondition
    ∷ Transformation.professionalDevelopmentCondition
    ∷ Transformation.policyCondition
    ∷ [] )
    ( institutionalDurabilityAndMonitoring
    ∷ epistemicAgencyAndPublicGovernance
    ∷ infrastructureOpennessAndInteroperability
    ∷ intergenerationalOptionPreservation
    ∷ [] )
    ( Primary.unescoESD2030MidtermSource
    ∷ Primary.uneceFifthESDEvaluationSource
    ∷ Scholarly.holstSDG47MonitoringSource
    ∷ Primary.unescoAICommonGoodMinisterialSource
    ∷ Prior.publicDigitalLearningPlatformCharterSource
    ∷ Scholarly.boehmeDigitainabilitySource
    ∷ [] )
    true refl
    "Transformative digital-ESD should be governed as an iterative institutional process: build professional and organisational capacity to monitor integration, outcomes and burden incidence; return evidence to affected participants; revise decisions; retain portability/exit options; and avoid locking current classifications or infrastructure choices into future generations."
    "Longitudinal input integration is not outcome transformation; present benefit does not determine later burden; future-option language is a DASHI synthesis constraint rather than a claim that the cited sources share one intergenerational theory."

canonicalTransformativePrincipleMatrix : List PrincipleConstraintRow
canonicalTransformativePrincipleMatrix =
  situatedRelationalEngagementConstraintRow
  ∷ feedbackAsRevisableSignalConstraintRow
  ∷ constitutiveLearnerAgencyConstraintRow
  ∷ adaptiveSupportWithLocalChoiceConstraintRow
  ∷ pluralSituatedObserversConstraintRow
  ∷ contextualCustodianshipConstraintRow
  ∷ iterativeEvidenceReturnAndRechartingConstraintRow
  ∷ []

transformativePrincipleMatrixRowCount : Nat
transformativePrincipleMatrixRowCount = 7

------------------------------------------------------------------------
-- Cross-corpus non-promotion firewalls.
------------------------------------------------------------------------

data PrincipleConstraintPairCreatesEmpiricalDigitalESDEffect : Set where
data SustainabilityEvidenceBecomesAliceSourceFinding : Set where
data AlicePrincipleCreatesLifecycleMeasurement : Set where
data NormativeConstraintCreatesDeploymentCompliance : Set where

principleConstraintPairDoesNotCreateEmpiricalDigitalESDEffect :
  PrincipleConstraintPairCreatesEmpiricalDigitalESDEffect → ⊥
principleConstraintPairDoesNotCreateEmpiricalDigitalESDEffect ()

sustainabilityEvidenceDoesNotBecomeAliceSourceFinding :
  SustainabilityEvidenceBecomesAliceSourceFinding → ⊥
sustainabilityEvidenceDoesNotBecomeAliceSourceFinding ()

alicePrincipleDoesNotCreateLifecycleMeasurement :
  AlicePrincipleCreatesLifecycleMeasurement → ⊥
alicePrincipleDoesNotCreateLifecycleMeasurement ()

normativeConstraintDoesNotCreateDeploymentCompliance :
  NormativeConstraintCreatesDeploymentCompliance → ⊥
normativeConstraintDoesNotCreateDeploymentCompliance ()

record TransformativePrincipleMatrixBoundary : Set where
  constructor transformative-principle-matrix-boundary
  field
    aliceAndSustainabilitySourceRolesSeparated : Bool
    aliceAndSustainabilitySourceRolesSeparatedIsTrue :
      aliceAndSustainabilitySourceRolesSeparated ≡ true
    selectedPairingsNotCartesianDecoration : Bool
    selectedPairingsNotCartesianDecorationIsTrue :
      selectedPairingsNotCartesianDecoration ≡ true
    scalingConditionsRetained : Bool
    scalingConditionsRetainedIsTrue : scalingConditionsRetained ≡ true
    externalityIncidenceAuditRetained : Bool
    externalityIncidenceAuditRetainedIsTrue : externalityIncidenceAuditRetained ≡ true
    environmentalSocialEconomicEpistemicInfrastructureDimensionsRetained : Bool
    environmentalSocialEconomicEpistemicInfrastructureDimensionsRetainedIsTrue :
      environmentalSocialEconomicEpistemicInfrastructureDimensionsRetained ≡ true
    participantAuthorityBoundaryRetained : Bool
    participantAuthorityBoundaryRetainedIsTrue :
      participantAuthorityBoundaryRetained ≡ true
    lifecycleMethodNotDeploymentMeasurement : Bool
    lifecycleMethodNotDeploymentMeasurementIsTrue :
      lifecycleMethodNotDeploymentMeasurement ≡ true
    longitudinalInputNotOutcomeTransformation : Bool
    longitudinalInputNotOutcomeTransformationIsTrue :
      longitudinalInputNotOutcomeTransformation ≡ true
    matrixCreatesEmpiricalDigitalESDEffect : Bool
    matrixCreatesEmpiricalDigitalESDEffectIsFalse :
      matrixCreatesEmpiricalDigitalESDEffect ≡ false
    matrixCandidateOnly : Bool
    matrixCandidateOnlyIsTrue : matrixCandidateOnly ≡ true

open TransformativePrincipleMatrixBoundary public

canonicalTransformativePrincipleMatrixBoundary : TransformativePrincipleMatrixBoundary
canonicalTransformativePrincipleMatrixBoundary =
  transformative-principle-matrix-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl

transformativePrincipleMatrixReading : String
transformativePrincipleMatrixReading =
  "The manuscript's generative centre is represented as seven source-attributed digital-education principles cross-pollinated with canonical scaling conditions and independent sustainability constraints. The A-side preserves the Alice Brown / colleague education corpus; the enactment layer retains scalable pedagogy, institutional practice, professional development and policy; the B-side preserves ESD, lifecycle, governance, TCO, interoperability, equity and longitudinal sources. The externality-incidence audit separately retains contribution, benefit, burden, voice, control/mediation, exit, lifecycle stage, temporal displacement and material position. Their pairing produces candidate digital-ESD design propositions, not empirical effects. This allows the paper to ask not only whether a proposed transformation works but who contributes, who benefits, who bears burdens, who controls or mediates the system, who has voice, who can exit, where in the lifecycle impacts arise, and whether future learner/institutional options remain open."
