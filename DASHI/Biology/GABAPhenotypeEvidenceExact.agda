module DASHI.Biology.GABAPhenotypeEvidenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.NeurochemicalVocabularyReceipt as Vocabulary
import DASHI.Biology.NeurotypeProcessingGeometryExact as Geometry

------------------------------------------------------------------------
-- GABA / PHENOTYPE EVIDENCE LAYER
--
-- This module is deliberately an evidence-and-promotion boundary, not a
-- neurodevelopmental causal theory.  It formalises the strongest safe shape
-- recoverable from the 2026-10-06 transcript audit:
--
--   named source -> population/region/measurement/task/phenotype receipt
--                -> bounded association claim
--                -/-> diagnosis, whole-brain state, causal necessity,
--                    causal sufficiency, attachment status, or another domain
--                    without an explicit downstream bridge receipt.
--
-- Attribution rule: externally sourced claims remain attached to named source
-- metadata and a role string.  Synthetic theorem witnesses below are marked as
-- synthetic and are not population estimates, diagnostic cut-offs, effect
-- sizes, or replacements for the cited studies.
------------------------------------------------------------------------

record LiteratureSource : Set where
  constructor literatureSource
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    role : String

open LiteratureSource public

schmitz2017Source : LiteratureSource
schmitz2017Source =
  literatureSource
    "Thomas W. Schmitz; Michael C. Correia; Catarina S. Ferreira; Adrian Prescot; Michael C. Anderson"
    "Hippocampal GABA enables inhibitory control over unwanted thoughts"
    "Nature Communications 8:1311"
    2017
    "10.1038/s41467-017-00956-z"
    "healthy-young-adult hippocampal GABA / Think-No-Think association; does not establish emotion suppression or diagnostic causation"

autismGABAMetaAnalysis2024Source : LiteratureSource
autismGABAMetaAnalysis2024Source =
  literatureSource
    "systematic-review / meta-analysis source registry row"
    "GABA concentration in autism spectrum disorder: a systematic review and meta-analysis of proton magnetic resonance spectroscopy studies"
    "2024 systematic review and meta-analysis"
    2024
    "PMID:38796123"
    "group-level autism/GABA synthesis; heterogeneous regional and methodological evidence, not causal sufficiency"

ptsdGABA2013Source : LiteratureSource
ptsdGABA2013Source =
  literatureSource
    "PTSD magnetic-resonance-spectroscopy study source registry row"
    "Reduced GABA in the anterior insula in posttraumatic stress disorder"
    "2013 magnetic resonance spectroscopy study"
    2013
    "PMID:23861191"
    "regional PTSD/GABA association fixture; does not define PTSD by GABA level"

ptsdMRSReview2022Source : LiteratureSource
ptsdMRSReview2022Source =
  literatureSource
    "systematic-review source registry row"
    "Magnetic resonance spectroscopy in post-traumatic stress disorder: an updated systematic review"
    "2022 systematic review"
    2022
    "PMID:36237981"
    "cross-study heterogeneity boundary for PTSD metabolite claims"

------------------------------------------------------------------------
-- Typed empirical coordinates.
------------------------------------------------------------------------

data PopulationKind : Set where
  healthyYoungAdults : PopulationKind
  autisticParticipants : PopulationKind
  adhdParticipants : PopulationKind
  ptsdParticipants : PopulationKind
  mixedOrMetaAnalyticPopulation : PopulationKind

data BrainRegion : Set where
  hippocampus : BrainRegion
  sensorimotorCortex : BrainRegion
  medialPrefrontalCortex : BrainRegion
  anteriorInsula : BrainRegion
  multipleOrMixedRegions : BrainRegion

data MeasurementKind : Set where
  protonMRS : MeasurementKind
  spectroscopyMetaAnalysis : MeasurementKind
  otherGABAMeasurement : MeasurementKind

data TaskKind : Set where
  thinkNoThinkTask : TaskKind
  sensoryTask : TaskKind
  symptomAssociation : TaskKind
  noSingleTask : TaskKind

data PhenotypeKind : Set where
  retrievalSuppressionPerformance : PhenotypeKind
  sensoryProcessingDifference : PhenotypeKind
  autismDiagnosticCoordinate : PhenotypeKind
  adhdDiagnosticCoordinate : PhenotypeKind
  ptsdDiagnosticCoordinate : PhenotypeKind
  attachmentSecurity : PhenotypeKind
  neuralSynchrony : PhenotypeKind
  neuroinflammation : PhenotypeKind
  emotionSuppression : PhenotypeKind

data Direction : Set where
  positiveAssociation : Direction
  negativeAssociation : Direction
  groupLower : Direction
  groupHigher : Direction
  heterogeneousOrMixed : Direction
  directionNotPromoted : Direction

data EvidenceClass : Set where
  observationalAssociation : EvidenceClass
  groupDifference : EvidenceClass
  systematicReviewEvidence : EvidenceClass
  causalInterventionEvidence : EvidenceClass
  syntheticBoundaryWitness : EvidenceClass

record RegionalGABAEvidence : Set where
  constructor regionalGABAEvidence
  field
    source : LiteratureSource
    population : PopulationKind
    region : BrainRegion
    measurement : MeasurementKind
    task : TaskKind
    phenotype : PhenotypeKind
    direction : Direction
    evidenceClass : EvidenceClass
    attributionBoundary : String

open RegionalGABAEvidence public

------------------------------------------------------------------------
-- Source-attached receipts.
------------------------------------------------------------------------

schmitz2017ThoughtSuppression : RegionalGABAEvidence
schmitz2017ThoughtSuppression =
  regionalGABAEvidence
    schmitz2017Source
    healthyYoungAdults
    hippocampus
    protonMRS
    thinkNoThinkTask
    retrievalSuppressionPerformance
    positiveAssociation
    observationalAssociation
    "Bound to the cited healthy-participant hippocampal Think/No-Think result; not promoted to emotion suppression, autism, ADHD, PTSD, or whole-brain GABA."

autismGABAMetaAnalysis2024 : RegionalGABAEvidence
autismGABAMetaAnalysis2024 =
  regionalGABAEvidence
    autismGABAMetaAnalysis2024Source
    mixedOrMetaAnalyticPopulation
    multipleOrMixedRegions
    spectroscopyMetaAnalysis
    noSingleTask
    autismDiagnosticCoordinate
    groupLower
    systematicReviewEvidence
    "Group-level meta-analytic direction only; heterogeneity and regional variation block individual classification and causal-sufficiency promotion."

ptsdAnteriorInsulaGABA2013 : RegionalGABAEvidence
ptsdAnteriorInsulaGABA2013 =
  regionalGABAEvidence
    ptsdGABA2013Source
    ptsdParticipants
    anteriorInsula
    protonMRS
    symptomAssociation
    ptsdDiagnosticCoordinate
    groupLower
    observationalAssociation
    "Regional case-control association only; not a definition, necessity theorem, or sufficient mechanism of PTSD."

------------------------------------------------------------------------
-- Existing-repo attachment.
------------------------------------------------------------------------

gabaVocabularyOwner = Vocabulary.gabaCandidate

autismCoordinateOwner : Geometry.NeurotypeCoordinate
autismCoordinateOwner = Geometry.autisticCoordinate

adhdCoordinateOwner : Geometry.NeurotypeCoordinate
adhdCoordinateOwner = Geometry.adhdCoordinate

audhdCoordinateOwner : Geometry.NeurotypeCoordinate
audhdCoordinateOwner = Geometry.audhdCoordinate

------------------------------------------------------------------------
-- Promotion gates.
--
-- These empty permission types encode absence of authority.  Downstream work
-- can introduce evidence-bearing adapters without changing the meaning of the
-- source receipts above.  No proposition here claims that a bridge is
-- impossible in nature; only that this module does not possess the receipt
-- required to promote the source claim.
------------------------------------------------------------------------

data AssociationIsCausalSufficiencyPermission : Set where

data RegionalDifferenceIsWholeBrainDifferencePermission : Set where

data GroupMeanClassifiesIndividualPermission : Set where

data DiagnosisDeterminesGABALevelPermission : Set where

data ThoughtSuppressionIsEmotionSuppressionPermission : Set where

data SynchronyDefinesAttachmentPermission : Set where

data GABADefinesNeuroinflammationPermission : Set where

data AutismCausedByLowGABAPermission : Set where

data ADHDCausedByLowGABAPermission : Set where

associationDoesNotImplyCausalSufficiency :
  AssociationIsCausalSufficiencyPermission → ⊥
associationDoesNotImplyCausalSufficiency ()

regionalGABADifferenceDoesNotImplyWholeBrainDifference :
  RegionalDifferenceIsWholeBrainDifferencePermission → ⊥
regionalGABADifferenceDoesNotImplyWholeBrainDifference ()

groupMeanDoesNotClassifyIndividual :
  GroupMeanClassifiesIndividualPermission → ⊥
groupMeanDoesNotClassifyIndividual ()

diagnosisDoesNotDetermineGABALevel :
  DiagnosisDeterminesGABALevelPermission → ⊥
diagnosisDoesNotDetermineGABALevel ()

thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression :
  ThoughtSuppressionIsEmotionSuppressionPermission → ⊥
thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression ()

noAttachmentBridgeFromSynchronyWithoutReceipt :
  SynchronyDefinesAttachmentPermission → ⊥
noAttachmentBridgeFromSynchronyWithoutReceipt ()

noNeuroinflammationBridgeFromGABAWithoutReceipt :
  GABADefinesNeuroinflammationPermission → ⊥
noNeuroinflammationBridgeFromGABAWithoutReceipt ()

autismLowGABAAssociationDoesNotProveCausalSufficiency :
  AutismCausedByLowGABAPermission → ⊥
autismLowGABAAssociationDoesNotProveCausalSufficiency ()

adhdGABAHypothesisDoesNotProveCausalSufficiency :
  ADHDCausedByLowGABAPermission → ⊥
adhdGABAHypothesisDoesNotProveCausalSufficiency ()

------------------------------------------------------------------------
-- Transcript-audit statuses.
------------------------------------------------------------------------

data AuditStatus : Set where
  supportedBounded : AuditStatus
  candidateAssociationOnly : AuditStatus
  needsNamedReceipt : AuditStatus
  blockedPromotion : AuditStatus
  domainBridgeMissing : AuditStatus

record TranscriptClaimAudit : Set where
  constructor transcriptClaimAudit
  field
    transcriptClaim : String
    status : AuditStatus
    basis : String

open TranscriptClaimAudit public

transcriptClaimAudits : List TranscriptClaimAudit
transcriptClaimAudits =
  transcriptClaimAudit
    "hippocampal GABA predicts successful thought suppression"
    supportedBounded
    "Schmitz et al. 2017 receipt: bounded to hippocampus, healthy young adults, and Think/No-Think retrieval suppression." ∷
  transcriptClaimAudit
    "the cited result specifically excludes emotional suppression"
    needsNamedReceipt
    "The bounded receipt does not carry an emotion-suppression comparison." ∷
  transcriptClaimAudit
    "autism has lower GABA"
    candidateAssociationOnly
    "2024 meta-analytic group-level direction with heterogeneity; no individual or universal diagnostic promotion." ∷
  transcriptClaimAudit
    "GABA is sufficient to create autism"
    blockedPromotion
    "Association/group-difference receipts do not contain causal-sufficiency authority." ∷
  transcriptClaimAudit
    "ADHD generally has lower GABA"
    needsNamedReceipt
    "No general low-GABA ADHD receipt is admitted by this module." ∷
  transcriptClaimAudit
    "higher GABA implies lower ADHD symptom severity"
    needsNamedReceipt
    "Requires named population, region, measurement, severity instrument, direction, and source." ∷
  transcriptClaimAudit
    "GABA is implicated in PTSD"
    candidateAssociationOnly
    "Regional spectroscopy evidence is representable; systematic review heterogeneity blocks definition or sufficiency." ∷
  transcriptClaimAudit
    "neural synchrony deficit means insecure attachment by definition"
    domainBridgeMissing
    "Synchrony and attachment are distinct phenotype domains; no definitional bridge receipt is present." ∷
  transcriptClaimAudit
    "GABA state determines neuroinflammation"
    domainBridgeMissing
    "Neurochemical and neuroinflammatory coordinates require an explicit empirical adapter." ∷ []

------------------------------------------------------------------------
-- Claim-boundary summary.
------------------------------------------------------------------------

record GABAPhenotypeBoundary : Set where
  constructor gabaPhenotypeBoundary
  field
    regionalEvidenceIsRepresentable : Bool
    regionalEvidenceIsRepresentableIsTrue : regionalEvidenceIsRepresentable ≡ true
    sourceAttributionIsRetained : Bool
    sourceAttributionIsRetainedIsTrue : sourceAttributionIsRetained ≡ true
    associationAutoPromotesToCausation : Bool
    associationAutoPromotesToCausationIsFalse : associationAutoPromotesToCausation ≡ false
    groupDifferenceAutoClassifiesIndividuals : Bool
    groupDifferenceAutoClassifiesIndividualsIsFalse : groupDifferenceAutoClassifiesIndividuals ≡ false
    diagnosisAutoDeterminesGABA : Bool
    diagnosisAutoDeterminesGABAIsFalse : diagnosisAutoDeterminesGABA ≡ false
    crossDomainAttachmentBridgeIsAutomatic : Bool
    crossDomainAttachmentBridgeIsAutomaticIsFalse : crossDomainAttachmentBridgeIsAutomatic ≡ false

canonicalGABAPhenotypeBoundary : GABAPhenotypeBoundary
canonicalGABAPhenotypeBoundary =
  gabaPhenotypeBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
