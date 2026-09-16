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

------------------------------------------------------------------------
-- PRE-SCREEN CANDIDATE SOURCE/SCOPE MATRIX
--
-- This is deliberately not the included corpus. It gives the paper a concrete
-- source/scope substrate before database execution while preserving the hard
-- boundary:
--
--   acquired candidate != screened/included source.
--
-- Every row therefore remains `candidateOnly = true`. The future structured
-- extraction object may reuse these coordinates only after the exact search,
-- deduplication and screening lineage admits the source.
------------------------------------------------------------------------

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
unescoRoadmapCandidate =
  candidate-source-scope-row
    Primary.unescoESD2030RoadmapSource
    Method.institutionalFrameworkEvidence
    ( Method.transformationBeyondTechnologyUseRQ
    ∷ Method.durabilityAndLongitudinalTransformationRQ
    ∷ [] )
    Method.bidirectionalReciprocalRelation
    "global ESD-for-2030 programme/framework; education-system transformation context"
    "2020-2030 programme horizon"
    "five ESD-for-2030 priority-action areas and a system-transformation implementation frame"
    "normative/programmatic framework; does not establish effect of a named digital intervention"
    true refl

unescoMidtermCandidate : CandidateSourceScopeRow
unescoMidtermCandidate =
  candidate-source-scope-row
    Primary.unescoESD2030MidtermSource
    Method.empiricalOutcomeEvidence
    ( Method.transformationBeyondTechnologyUseRQ
    ∷ Method.durabilityAndLongitudinalTransformationRQ
    ∷ [] )
    Method.bidirectionalReciprocalRelation
    "global programme-level evaluation of ESD for 2030 across Member-State/partner implementation"
    "evaluation period 2021-2024, published 2026"
    "substantial implementation activity can coexist with limited systemic transformation; identifies coherence, monitoring and ownership needs"
    "programme-level mixed-methods evaluation; not a causal estimate for this manuscript's digital-ESD framework"
    true refl

oecdOutlook2026Candidate : CandidateSourceScopeRow
oecdOutlook2026Candidate =
  candidate-source-scope-row
    Primary.oecdDigitalEducationOutlook2026Source
    Method.reviewSynthesisEvidence
    ( Method.digitalEducationBuildsESDCapacityRQ
    ∷ Method.transformationBeyondTechnologyUseRQ
    ∷ [] )
    Method.digitalEducationToESDCapacity
    "international digital/GenAI education evidence and policy synthesis"
    "evidence available to OECD Digital Education Outlook 2026"
    "task performance with GenAI does not automatically imply learning; pedagogical intent, human-centred design, research, policy and infrastructure remain material conditions"
    "does not establish learning or sustainability effects for every technology, learner population or institution"
    true refl

unescoAICommonGoodCandidate : CandidateSourceScopeRow
unescoAICommonGoodCandidate =
  candidate-source-scope-row
    Primary.unescoAICommonGoodMinisterialSource
    Method.institutionalFrameworkEvidence
    ( Method.sustainabilityConstrainsDigitalEducationRQ
    ∷ Method.participantAgencyAndGovernanceRQ
    ∷ [] )
    Method.sustainabilityToDigitalEducationConstraint
    "intergovernmental AI/digital-education governance statement convened through UNESCO Digital Learning Week 2026"
    "adopted September 2026"
    "education as a human right/common good; deliberative governance, public accountability, rights, and source-bounded procurement/infrastructure principles"
    "normative governance statement; does not establish intervention effectiveness, sustainability outcome or local participant authority"
    true refl

gianniniTwinTransitionCandidate : CandidateSourceScopeRow
gianniniTwinTransitionCandidate =
  candidate-source-scope-row
    Prior.gianniniTwinTransitionSource
    Method.institutionalFrameworkEvidence
    ( Method.digitalEducationBuildsESDCapacityRQ
    ∷ Method.sustainabilityConstrainsDigitalEducationRQ
    ∷ [] )
    Method.bidirectionalReciprocalRelation
    "global UNESCO green/digital transition framing through education"
    "2024 policy/conceptual horizon"
    "green and digital transitions may be distinct or in tension; education can help align them"
    "antecedent framing only; does not prove automatic synergy or intervention effectiveness"
    true refl

publicPlatformCharterCandidate : CandidateSourceScopeRow
publicPlatformCharterCandidate =
  candidate-source-scope-row
    Prior.publicDigitalLearningPlatformCharterSource
    Method.institutionalFrameworkEvidence
    ( Method.sustainabilityConstrainsDigitalEducationRQ
    ∷ Method.participantAgencyAndGovernanceRQ
    ∷ Method.durabilityAndLongitudinalTransformationRQ
    ∷ [] )
    Method.sustainabilityToDigitalEducationConstraint
    "public digital learning platforms / education-system infrastructure governance"
    "2026 charter / design-governance horizon"
    "public accountability, inclusion, pedagogical purpose, openness, interoperability and trustworthiness are explicit platform principles"
    "normative charter; does not prove deployed platform durability, interoperability persistence or learning effect"
    true refl

ituL1410Candidate : CandidateSourceScopeRow
ituL1410Candidate =
  candidate-source-scope-row
    ICT.ituL1410LifecycleMethodSource
    Method.infrastructureLifecycleEvidence
    ( Method.sustainabilityConstrainsDigitalEducationRQ
    ∷ Method.durabilityAndLongitudinalTransformationRQ
    ∷ [] )
    Method.sustainabilityToDigitalEducationConstraint
    "ICT goods, networks and services; lifecycle-assessment method scope"
    "in-force November 2024 recommendation"
    "defines ICT LCA framework/guidance and comparative analysis against a reference product system"
    "method authority only; no same-object digital-ESD life-cycle inventory or comparative result"
    true refl

ituL1023Candidate : CandidateSourceScopeRow
ituL1023Candidate =
  candidate-source-scope-row
    ICT.ituL1023CircularityMethodSource
    Method.infrastructureLifecycleEvidence
    ( Method.sustainabilityConstrainsDigitalEducationRQ
    ∷ Method.durabilityAndLongitudinalTransformationRQ
    ∷ [] )
    Method.sustainabilityToDigitalEducationConstraint
    "ICT product circularity performance method scope"
    "in-force August 2023 recommendation"
    "defines circularity scoring coordinates including durability, repair, reuse, recycle and upgrade aspects"
    "method authority only; no same-object circularity score, repair support, service-life or durability observation"
    true refl

canonicalCandidateSourceScopeMatrix : List CandidateSourceScopeRow
canonicalCandidateSourceScopeMatrix =
  unescoRoadmapCandidate
  ∷ unescoMidtermCandidate
  ∷ oecdOutlook2026Candidate
  ∷ unescoAICommonGoodCandidate
  ∷ gianniniTwinTransitionCandidate
  ∷ publicPlatformCharterCandidate
  ∷ ituL1410Candidate
  ∷ ituL1023Candidate
  ∷ []

candidateSourceCount : Nat
candidateSourceCount = 8

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data PreScreenMatrixCreatesIncludedCorpus : Set where
data PreScreenMatrixClosesStructuredSearch : Set where
data CandidateRoleCreatesSameObjectEvidence : Set where
data CandidateMatrixCreatesEvidenceCompleteness : Set where

preScreenMatrixDoesNotCreateIncludedCorpus :
  PreScreenMatrixCreatesIncludedCorpus → ⊥
preScreenMatrixDoesNotCreateIncludedCorpus ()

preScreenMatrixDoesNotCloseStructuredSearch :
  PreScreenMatrixClosesStructuredSearch → ⊥
preScreenMatrixDoesNotCloseStructuredSearch ()

candidateRoleDoesNotCreateSameObjectEvidence :
  CandidateRoleCreatesSameObjectEvidence → ⊥
candidateRoleDoesNotCreateSameObjectEvidence ()

candidateMatrixDoesNotCreateEvidenceCompleteness :
  CandidateMatrixCreatesEvidenceCompleteness → ⊥
candidateMatrixDoesNotCreateEvidenceCompleteness ()

record SourceScopeMatrixBoundary : Set where
  constructor source-scope-matrix-boundary
  field
    allRowsCandidateOnly : Bool
    allRowsCandidateOnlyIsTrue : allRowsCandidateOnly ≡ true
    sourceRolesRetained : Bool
    sourceRolesRetainedIsTrue : sourceRolesRetained ≡ true
    populationAndTimeScopesRetained : Bool
    populationAndTimeScopesRetainedIsTrue :
      populationAndTimeScopesRetained ≡ true
    limitationsAndResidualsRetained : Bool
    limitationsAndResidualsRetainedIsTrue :
      limitationsAndResidualsRetained ≡ true
    preScreenMatrixIsIncludedCorpus : Bool
    preScreenMatrixIsIncludedCorpusIsFalse :
      preScreenMatrixIsIncludedCorpus ≡ false
    preScreenMatrixClosesStructuredSearch : Bool
    preScreenMatrixClosesStructuredSearchIsFalse :
      preScreenMatrixClosesStructuredSearch ≡ false
    candidateRowsCreateSameObjectEvidence : Bool
    candidateRowsCreateSameObjectEvidenceIsFalse :
      candidateRowsCreateSameObjectEvidence ≡ false

open SourceScopeMatrixBoundary public

canonicalSourceScopeMatrixBoundary : SourceScopeMatrixBoundary
canonicalSourceScopeMatrixBoundary =
  source-scope-matrix-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
