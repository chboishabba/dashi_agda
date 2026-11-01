module DASHI.Education.DigitalESDPreScreenCandidateSourceScopeMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDManuscriptMethodologyExact as Method
import DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact as Primary
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Prior
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Scholarly

record CandidateSourceScopeRow : Set where
  constructor candidate-source-scope-row
  field
    source : Attr.AttributedSource
    sourceRole : Method.EvidenceRole
    researchQuestions : List Method.ManuscriptResearchQuestion
    reciprocityDirection : Method.ReciprocityDirection
    populationOrSystemScope : String
    timeHorizon : String
    claimPaid : String
    limitationOrResidual : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open CandidateSourceScopeRow public

unescoRoadmapCandidate : CandidateSourceScopeRow
unescoRoadmapCandidate = candidate-source-scope-row Primary.unescoESD2030RoadmapSource Method.institutionalFrameworkEvidence (Method.transformationBeyondTechnologyUseRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.bidirectionalReciprocalRelation "global ESD-for-2030 programme/framework; education-system transformation context" "2020-2030 programme horizon" "five ESD-for-2030 priority-action areas and a system-transformation implementation frame" "normative/programmatic framework; does not establish effect of a named digital intervention" true refl

unescoMidtermCandidate : CandidateSourceScopeRow
unescoMidtermCandidate = candidate-source-scope-row Primary.unescoESD2030MidtermSource Method.empiricalOutcomeEvidence (Method.transformationBeyondTechnologyUseRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.bidirectionalReciprocalRelation "global programme-level evaluation of ESD for 2030 across Member-State/partner implementation" "evaluation period 2021-2024, published 2026" "substantial implementation activity can coexist with limited systemic transformation; identifies coherence, monitoring and ownership needs" "programme-level mixed-methods evaluation; not a causal estimate for this manuscript's digital-ESD framework" true refl

oecdOutlook2026Candidate : CandidateSourceScopeRow
oecdOutlook2026Candidate = candidate-source-scope-row Primary.oecdDigitalEducationOutlook2026Source Method.reviewSynthesisEvidence (Method.digitalEducationBuildsESDCapacityRQ ∷ Method.transformationBeyondTechnologyUseRQ ∷ []) Method.digitalEducationToESDCapacity "international digital/GenAI education evidence and policy synthesis" "evidence available to OECD Digital Education Outlook 2026" "task performance with GenAI does not automatically imply learning; pedagogical intent, human-centred design, research, policy and infrastructure remain material conditions" "does not establish learning or sustainability effects for every technology, learner population or institution" true refl

uneceFifthESDEvaluationCandidate : CandidateSourceScopeRow
uneceFifthESDEvaluationCandidate = candidate-source-scope-row Primary.uneceFifthESDEvaluationSource Method.reviewSynthesisEvidence (Method.transformationBeyondTechnologyUseRQ ∷ Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.bidirectionalReciprocalRelation "UNECE regional ESD implementation synthesis based on 31 national reports" "implementation phase 2021-2025; report March 2026" "digital access/tools/platforms are expanding across national systems while intentional integration of sustainability principles into digital-education policies/practices remains limited and digital-ESD/whole-institution approaches remain uneven" "regional national-report synthesis; does not establish causal intervention effects, local outcomes, or automatic transfer beyond the UNECE reporting population" true refl

unescoAICommonGoodCandidate : CandidateSourceScopeRow
unescoAICommonGoodCandidate = candidate-source-scope-row Primary.unescoAICommonGoodMinisterialSource Method.institutionalFrameworkEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.participantAgencyAndGovernanceRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "adopted intergovernmental AI/digital-education governance statement convened through UNESCO Digital Learning Week 2026" "adopted 8 September 2026" "education as a human right/common good; deliberative governance, public accountability, rights, total cost of ownership, interoperability, portability and open systems" "adopted normative governance statement; does not establish intervention effectiveness, sustainability outcome or local participant authority" true refl

unescoAIConsultationDiscussionCandidate : CandidateSourceScopeRow
unescoAIConsultationDiscussionCandidate = candidate-source-scope-row Primary.unescoAICommonGoodDiscussionSource Method.institutionalFrameworkEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.participantAgencyAndGovernanceRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "UNESCO discussion-paper and global-consultation process on AI governance in education" "consultation opened September 2026; comments feed 2027 policy briefs" "deliberative-governance framing, public-purpose questions and consultation agenda for AI in education" "discussion/consultation source only; not the adopted ministerial statement, not settled policy, and not intervention-effect evidence" true refl

unescoAIProcurementBackgroundCandidate : CandidateSourceScopeRow
unescoAIProcurementBackgroundCandidate = candidate-source-scope-row Primary.unescoAIProcurementBackgroundSource Method.institutionalFrameworkEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.participantAgencyAndGovernanceRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "UNESCO-commissioned AI procurement background paper for education governance" "2026 consultation background; feeds future policy briefs" "procurement is treated as a governance lever; supports extracting vendor, accountability, auditability, portability and procurement-condition coordinates" "consultation background only; not adopted policy and does not prove a procurement choice or deployed system satisfies those conditions" true refl

unescoAITCOBackgroundCandidate : CandidateSourceScopeRow
unescoAITCOBackgroundCandidate = candidate-source-scope-row Primary.unescoAITCOBackgroundSource Method.institutionalFrameworkEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "UNESCO-commissioned total-cost-of-ownership background paper for AI in education systems" "2026 consultation background; lifecycle/system-cost framing" "supports treating acquisition price as narrower than total cost of ownership and retaining lifecycle/system cost coordinates in procurement analysis" "background framing only; not a deployment-specific cost model, lifecycle inventory or sustainability result" true refl

ardilaDigitalFuturesCandidate : CandidateSourceScopeRow
ardilaDigitalFuturesCandidate = candidate-source-scope-row Scholarly.ardilaDigitalFuturesSource Method.empiricalOutcomeEvidence (Method.digitalEducationBuildsESDCapacityRQ ∷ Method.transformationBeyondTechnologyUseRQ ∷ Method.participantAgencyAndGovernanceRQ ∷ []) Method.digitalEducationToESDCapacity "two postgraduate Education and Technology student design teams at a London-based university; n=10" "ten-week design-thinking module in 2023; article 2025" "context-bounded evidence that design-thinking practices can foster or hinder sustainability competencies while students co-design digital educational technologies" "small reflective case study; does not establish universal learning effects, infrastructure sustainability or constitutive authority beyond the studied teams" true refl

gousetiPlatformisationCandidate : CandidateSourceScopeRow
gousetiPlatformisationCandidate = candidate-source-scope-row Scholarly.gousetiPlatformisationSource Method.empiricalOutcomeEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.participantAgencyAndGovernanceRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "school leaders, teachers, students and parents in two English secondary schools" "fieldwork April-May 2024 and September-October 2024; article 2026" "situated platformisation experiences including administrative/pedagogical benefits plus monitoring, surveillance, digital exclusion and teacher digital wellbeing" "two-school qualitative context; does not universalise platform effects, environmental sustainability or durability" true refl

zagamiAustralianEdtechCandidate : CandidateSourceScopeRow
zagamiAustralianEdtechCandidate = candidate-source-scope-row Scholarly.zagamiAustralianEdtechSource Method.contextualComparatorEvidence (Method.transformationBeyondTechnologyUseRQ ∷ Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "four Australian edtech cases: Canva for Education, Education Perfect, LearningField and Grok Academy" "comparative historical trajectories analysed in 2026" "governance, funding, legitimacy and sustainable-capital alignment shape edtech emergence, expansion, crisis, collapse and consolidation; includes interoperability/procurement tensions in case histories" "comparative public-document case study; does not establish universal durability, interoperability or causal success rules" true refl

chughSustainabilityParadoxCandidate : CandidateSourceScopeRow
chughSustainabilityParadoxCandidate = candidate-source-scope-row Scholarly.chughSustainabilityParadoxSource Method.contextualComparatorEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "opinion/conceptual paper focused primarily on higher-education digital sustainability" "published March 2026; lifecycle-oriented conceptual horizon" "close prior-art framing: digital education can support access/participation while increasing energy/material impacts and inequalities; recommends lifecycle, procurement and circularity responses" "opinion paper; no empirical intervention effect. Pays the sustainability-paradox antecedent but not same-object payment discipline, participant-authority or structured-review contributions" true refl

boehmeDigitainabilityCandidate : CandidateSourceScopeRow
boehmeDigitainabilityCandidate = candidate-source-scope-row Scholarly.boehmeDigitainabilitySource Method.contextualComparatorEvidence (Method.transformationBeyondTechnologyUseRQ ∷ Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.participantAgencyAndGovernanceRQ ∷ []) Method.bidirectionalReciprocalRelation "conceptual-synthetic reconstruction of ESD and digitality debates in Germany, Austria and Switzerland" "published May 2026; conceptual twin-transformation horizon" "close prior-art framing of sustainability/ESD and digitality as a mutually coupled twin transformation, including sustainable digitality and sustainability under conditions of digitality" "conceptual/purposive synthesis; not empirical effect evidence. Pays coupled twin-transformation positioning but not same-object evidence payment, participant-authority receipts, or dependency-aware structured-search lineage" true refl

holstSDG47MonitoringCandidate : CandidateSourceScopeRow
holstSDG47MonitoringCandidate = candidate-source-scope-row Scholarly.holstSDG47MonitoringSource Method.longitudinalDurabilityEvidence (Method.transformationBeyondTechnologyUseRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.digitalEducationToESDCapacity "all formal education sectors in Germany; more than 11,000 policy/curriculum/training/assessment documents" "ten-year longitudinal input-monitoring window; article 2024" "operationalises depth and speed of ESD integration and argues for independent integrative monitoring across input, process, output and outcome" "input-indicator evidence only; does not itself establish learning, output/outcome transformation, digital-ESD effects or transfer beyond the monitoring context" true refl

martinezDigitalEducationReviewCandidate : CandidateSourceScopeRow
martinezDigitalEducationReviewCandidate = candidate-source-scope-row Scholarly.martinezDigitalEducationSystematicReviewSource Method.reviewSynthesisEvidence (Method.digitalEducationBuildsESDCapacityRQ ∷ Method.transformationBeyondTechnologyUseRQ ∷ Method.sustainabilityConstrainsDigitalEducationRQ ∷ []) Method.digitalEducationToESDCapacity "33 peer-reviewed empirical studies in face-to-face compulsory primary/secondary schooling; review sources Scopus, Web of Science and reference checking" "studies published 2012-June 2025; review published August 2026" "digital education is often conflated with ICT use/digital competence; positive outcomes depend on pedagogical intentionality, teacher mediation, coherent policy/infrastructure and equitable access, while low-cognitive-demand use remains common" "systematic-review synthesis rather than a same-object intervention effect. Its Scopus/WoS search belongs to that review and does not pay this manuscript's database execution receipts" true refl

gianniniTwinTransitionCandidate : CandidateSourceScopeRow
gianniniTwinTransitionCandidate = candidate-source-scope-row Prior.gianniniTwinTransitionSource Method.institutionalFrameworkEvidence (Method.digitalEducationBuildsESDCapacityRQ ∷ Method.sustainabilityConstrainsDigitalEducationRQ ∷ []) Method.bidirectionalReciprocalRelation "global UNESCO green/digital transition framing through education" "2024 policy/conceptual horizon" "green and digital transitions may be distinct or in tension; education can help align them" "antecedent framing only; does not prove automatic synergy or intervention effectiveness" true refl

publicPlatformCharterCandidate : CandidateSourceScopeRow
publicPlatformCharterCandidate = candidate-source-scope-row Prior.publicDigitalLearningPlatformCharterSource Method.institutionalFrameworkEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.participantAgencyAndGovernanceRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "public digital learning platforms / education-system infrastructure governance" "2026 charter / design-governance horizon" "public accountability, inclusion, pedagogical purpose, openness, interoperability and trustworthiness are explicit platform principles" "normative charter; does not prove deployed platform durability, interoperability persistence or learning effect" true refl

ituL1410Candidate : CandidateSourceScopeRow
ituL1410Candidate = candidate-source-scope-row ICT.ituL1410LifecycleMethodSource Method.infrastructureLifecycleEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "ICT goods, networks and services; lifecycle-assessment method scope" "in-force November 2024 recommendation" "defines ICT LCA framework/guidance and comparative analysis against a reference product system" "method authority only; no same-object digital-ESD life-cycle inventory or comparative result" true refl

ituL1023Candidate : CandidateSourceScopeRow
ituL1023Candidate = candidate-source-scope-row ICT.ituL1023CircularityMethodSource Method.infrastructureLifecycleEvidence (Method.sustainabilityConstrainsDigitalEducationRQ ∷ Method.durabilityAndLongitudinalTransformationRQ ∷ []) Method.sustainabilityToDigitalEducationConstraint "ICT product circularity performance method scope" "in-force August 2023 recommendation" "defines circularity scoring coordinates including durability, repair, reuse, recycle and upgrade aspects" "method authority only; no same-object circularity score, repair support, service-life or durability observation" true refl

canonicalCandidateSourceScopeMatrix : List CandidateSourceScopeRow
canonicalCandidateSourceScopeMatrix = unescoRoadmapCandidate ∷ unescoMidtermCandidate ∷ oecdOutlook2026Candidate ∷ uneceFifthESDEvaluationCandidate ∷ unescoAICommonGoodCandidate ∷ unescoAIConsultationDiscussionCandidate ∷ unescoAIProcurementBackgroundCandidate ∷ unescoAITCOBackgroundCandidate ∷ ardilaDigitalFuturesCandidate ∷ gousetiPlatformisationCandidate ∷ zagamiAustralianEdtechCandidate ∷ chughSustainabilityParadoxCandidate ∷ boehmeDigitainabilityCandidate ∷ holstSDG47MonitoringCandidate ∷ martinezDigitalEducationReviewCandidate ∷ gianniniTwinTransitionCandidate ∷ publicPlatformCharterCandidate ∷ ituL1410Candidate ∷ ituL1023Candidate ∷ []

candidateSourceCount : Nat
candidateSourceCount = 19

data PreScreenMatrixCreatesIncludedCorpus : Set where
data PreScreenMatrixClosesStructuredSearch : Set where
data CandidateRoleCreatesSameObjectEvidence : Set where
data CandidateMatrixCreatesEvidenceCompleteness : Set where

preScreenMatrixDoesNotCreateIncludedCorpus : PreScreenMatrixCreatesIncludedCorpus → ⊥
preScreenMatrixDoesNotCreateIncludedCorpus ()

preScreenMatrixDoesNotCloseStructuredSearch : PreScreenMatrixClosesStructuredSearch → ⊥
preScreenMatrixDoesNotCloseStructuredSearch ()

candidateRoleDoesNotCreateSameObjectEvidence : CandidateRoleCreatesSameObjectEvidence → ⊥
candidateRoleDoesNotCreateSameObjectEvidence ()

candidateMatrixDoesNotCreateEvidenceCompleteness : CandidateMatrixCreatesEvidenceCompleteness → ⊥
candidateMatrixDoesNotCreateEvidenceCompleteness ()

record SourceScopeMatrixBoundary : Set where
  constructor source-scope-matrix-boundary
  field
    allRowsCandidateOnly : Bool
    allRowsCandidateOnlyIsTrue : allRowsCandidateOnly ≡ true
    sourceRolesRetained : Bool
    sourceRolesRetainedIsTrue : sourceRolesRetained ≡ true
    populationAndTimeScopesRetained : Bool
    populationAndTimeScopesRetainedIsTrue : populationAndTimeScopesRetained ≡ true
    limitationsAndResidualsRetained : Bool
    limitationsAndResidualsRetainedIsTrue : limitationsAndResidualsRetained ≡ true
    preScreenMatrixIsIncludedCorpus : Bool
    preScreenMatrixIsIncludedCorpusIsFalse : preScreenMatrixIsIncludedCorpus ≡ false
    preScreenMatrixClosesStructuredSearch : Bool
    preScreenMatrixClosesStructuredSearchIsFalse : preScreenMatrixClosesStructuredSearch ≡ false
    candidateRowsCreateSameObjectEvidence : Bool
    candidateRowsCreateSameObjectEvidenceIsFalse : candidateRowsCreateSameObjectEvidence ≡ false

open SourceScopeMatrixBoundary public

canonicalSourceScopeMatrixBoundary : SourceScopeMatrixBoundary
canonicalSourceScopeMatrixBoundary = source-scope-matrix-boundary true refl true refl true refl true refl false refl false refl false refl
