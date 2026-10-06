module DASHI.Biology.GABAPhenotypeEvidenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.NeurochemicalVocabularyReceipt as Vocabulary
import DASHI.Biology.NeurotypeProcessingGeometryExact as Geometry
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.CandidateOnlyCore as CandidateOnlyCore

------------------------------------------------------------------------
-- GABA / PHENOTYPE EVIDENCE LAYER
--
-- This is an evidence-and-promotion boundary, not a neurodevelopmental causal
-- theory.  The source-side shape is:
--
--   attributed source
--     -> population / region / measurement / task / phenotype receipt
--     -> bounded empirical relation
--     -/-> whole-brain state, individual diagnosis, causal necessity,
--         causal sufficiency, attachment status, neuroinflammation, or an
--         uncited cross-domain mechanism.
--
-- Attribution follows DASHI.Core.AttributedSourceCore.  A citation identifies
-- provenance and its relationship to this formalisation; it imports neither
-- proof nor scientific authority.  No synthetic carrier below is an empirical
-- effect size, diagnostic threshold, or population estimate.
------------------------------------------------------------------------

schmitz2017Source : Source.AttributedSource
schmitz2017Source =
  Source.mkDOISource
    "Taylor W. Schmitz; Marta M. Correia; Catarina S. Ferreira; Andrew P. Prescot; Michael C. Anderson"
    "Hippocampal GABA enables inhibitory control over unwanted thoughts"
    "Nature Communications 8:1311"
    "2017"
    "10.1038/s41467-017-00956-z"
    "https://doi.org/10.1038/s41467-017-00956-z"
    Source.academicArticleSource
    "Pays the healthy-young-adult hippocampal GABA / Think-No-Think retrieval-suppression association. It does not pay emotion suppression, diagnosis, or causal sufficiency."
    Source.publicAttribution

autismGABAMetaAnalysis2024Source : Source.AttributedSource
autismGABAMetaAnalysis2024Source =
  Source.mkDOISource
    "Alice R. Thomson; Duanghathai Pasanta; Tomoki Arichi; Nicolaas A. Puts"
    "Neurometabolite differences in Autism as assessed with Magnetic Resonance Spectroscopy: A systematic review and meta-analysis"
    "Neuroscience & Biobehavioral Reviews 162:105728"
    "2024"
    "10.1016/j.neubiorev.2024.105728"
    "https://doi.org/10.1016/j.neubiorev.2024.105728"
    Source.academicArticleSource
    "Pays a group-level meta-analytic autism/GABA direction while retaining demographic, regional, and methodological heterogeneity. It does not classify individuals or prove causal sufficiency."
    Source.publicAttribution

puts2017Source : Source.AttributedSource
puts2017Source =
  Source.mkDOISource
    "Nicolaas A. J. Puts; Ericka L. Wodka; Ashley D. Harris; Deana Crocetti; Mark Tommerdahl; Stewart H. Mostofsky; Richard A. E. Edden"
    "Reduced GABA and altered somatosensory function in children with autism spectrum disorder"
    "Autism Research 10(4):608-619"
    "2017"
    "10.1002/aur.1691"
    "https://doi.org/10.1002/aur.1691"
    Source.academicArticleSource
    "Pays reduced sensorimotor GABA in the studied autistic-child cohort and task-specific associations with tactile measures; occipital GABA was not reduced."
    Source.publicAttribution

umesawa2020Source : Source.AttributedSource
umesawa2020Source =
  Source.mkDOISource
    "Yumi Umesawa; Takeshi Atsumi; Mrinmoy Chakrabarty; Reiko Fukatsu; Masakazu Ide"
    "GABA Concentration in the Left Ventral Premotor Cortex Associates With Sensory Hyper-Responsiveness in Autism Spectrum Disorders Without Intellectual Disability"
    "Frontiers in Neuroscience 14:482"
    "2020"
    "10.3389/fnins.2020.00482"
    "https://doi.org/10.3389/fnins.2020.00482"
    Source.academicArticleSource
    "Pays a negative association between left ventral premotor-cortex GABA and sensory hyper-responsiveness in the studied cohort; it does not universalise a sensory-severity law."
    Source.publicAttribution

ptsdGABA2014Source : Source.AttributedSource
ptsdGABA2014Source =
  Source.mkDOISource
    "Isabelle M. Rosso; Melissa R. Weiner; David J. Crowley; Marisa M. Silveri; Scott L. Rauch; J. Eric Jensen"
    "Insula and anterior cingulate GABA levels in posttraumatic stress disorder: preliminary findings using magnetic resonance spectroscopy"
    "Depression and Anxiety 31(2):115-123"
    "2014"
    "10.1002/da.22155"
    "https://doi.org/10.1002/da.22155"
    Source.academicArticleSource
    "Pays the preliminary right-anterior-insula group difference; dorsal ACC did not significantly differ and insula GABA was not significantly associated with PTSD symptom severity."
    Source.publicAttribution

ptsdMRSReview2022Source : Source.AttributedSource
ptsdMRSReview2022Source =
  Source.mkDOISource
    "Kelley M. Swanberg; Leonardo Campos; Chadi G. Abdallah; Christoph Juchem"
    "Proton Magnetic Resonance Spectroscopy in Post-Traumatic Stress Disorder-Updated Systematic Review and Meta-Analysis"
    "Chronic Stress 6:24705470221128004"
    "2022"
    "10.1177/24705470221128004"
    "https://doi.org/10.1177/24705470221128004"
    Source.academicArticleSource
    "Pays the cross-study MRS review boundary: the strongest replicated meta-analytic signal was not a general GABA law, and heterogeneity varied widely across analyses."
    Source.publicAttribution

transcriptSource : Source.AttributedSource
transcriptSource =
  Source.mkNoDOISource
    "unidentified speaker in user-supplied transcript"
    "transcript-2026-10-06 (1).srt"
    "user-supplied SRT transcript"
    "2026"
    ""
    Source.archivalSource
    "Primary source for the claims audited below. Speaker identity is not inferred. External scientific support is represented only by separate attributed-source receipts."
    Source.existenceOnlyAttribution

canonicalEvidenceSources : List Source.AttributedSource
canonicalEvidenceSources =
  schmitz2017Source ∷
  autismGABAMetaAnalysis2024Source ∷
  puts2017Source ∷
  umesawa2020Source ∷
  ptsdGABA2014Source ∷
  ptsdMRSReview2022Source ∷ []

canonicalSourceAtlas : Source.AttributedSourceAtlas
canonicalSourceAtlas =
  Source.mkSourceAtlas
    "GABA phenotype evidence atlas"
    "DASHI.Biology.GABAPhenotypeEvidenceExact"
    canonicalEvidenceSources
    "Named scientific sources supporting bounded GABA/phenotype receipts; citations do not promote claims beyond the named study scope."

canonicalSourceAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority canonicalSourceAtlas ≡ false
canonicalSourceAtlasDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Typed empirical coordinates.
------------------------------------------------------------------------

data PopulationKind : Set where
  healthyYoungAdults : PopulationKind
  autisticChildren : PopulationKind
  autisticParticipantsWithoutID : PopulationKind
  autisticParticipants : PopulationKind
  adhdParticipants : PopulationKind
  ptsdParticipants : PopulationKind
  mixedOrMetaAnalyticPopulation : PopulationKind

data BrainRegion : Set where
  hippocampus : BrainRegion
  sensorimotorCortex : BrainRegion
  occipitalCortex : BrainRegion
  leftVentralPremotorCortex : BrainRegion
  medialPrefrontalCortex : BrainRegion
  anteriorInsula : BrainRegion
  dorsalAnteriorCingulate : BrainRegion
  multipleOrMixedRegions : BrainRegion

data MeasurementKind : Set where
  protonMRS : MeasurementKind
  gabaEditedMRS : MeasurementKind
  spectroscopyMetaAnalysis : MeasurementKind
  otherGABAMeasurement : MeasurementKind

data TaskKind : Set where
  thinkNoThinkTask : TaskKind
  tactileTaskBattery : TaskKind
  sensoryQuestionnaire : TaskKind
  symptomAssociation : TaskKind
  noSingleTask : TaskKind

data PhenotypeKind : Set where
  retrievalSuppressionPerformance : PhenotypeKind
  tactileProcessingDifference : PhenotypeKind
  sensoryHyperResponsiveness : PhenotypeKind
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
  noSignificantGroupDifference : Direction
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
    source : Source.AttributedSource
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
    "Greater resting hippocampal GABA predicted better mnemonic control in the study. The functional-specificity comparison was action stopping, not emotional suppression."

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
    "Overall lower GABA at group level in the meta-analysis; demographic, regional, and methodological variation remains explicit and blocks individual or universal promotion."

puts2017SensorimotorGABA : RegionalGABAEvidence
puts2017SensorimotorGABA =
  regionalGABAEvidence
    puts2017Source
    autisticChildren
    sensorimotorCortex
    gabaEditedMRS
    tactileTaskBattery
    tactileProcessingDifference
    groupLower
    groupDifference
    "Sensorimotor GABA was lower in the studied autistic-child group; occipital GABA was reported as normal. Several tactile associations were task-specific, so this row does not encode a scalar symptom-severity law."

umesawa2020SensoryHyperResponsiveness : RegionalGABAEvidence
umesawa2020SensoryHyperResponsiveness =
  regionalGABAEvidence
    umesawa2020Source
    autisticParticipantsWithoutID
    leftVentralPremotorCortex
    protonMRS
    sensoryQuestionnaire
    sensoryHyperResponsiveness
    negativeAssociation
    observationalAssociation
    "Lower left-vPMC GABA was associated with greater sensory hyper-responsiveness in the studied ASD group; region, cohort, and instrument remain part of the receipt."

ptsdAnteriorInsulaGABA2014 : RegionalGABAEvidence
ptsdAnteriorInsulaGABA2014 =
  regionalGABAEvidence
    ptsdGABA2014Source
    ptsdParticipants
    anteriorInsula
    protonMRS
    symptomAssociation
    ptsdDiagnosticCoordinate
    groupLower
    groupDifference
    "Right anterior-insula GABA was lower in the preliminary PTSD sample; dorsal ACC did not significantly differ, and insula GABA was not significantly associated with PTSD symptom severity."

ptsdMRSReview2022 : RegionalGABAEvidence
ptsdMRSReview2022 =
  regionalGABAEvidence
    ptsdMRSReview2022Source
    mixedOrMetaAnalyticPopulation
    multipleOrMixedRegions
    spectroscopyMetaAnalysis
    noSingleTask
    ptsdDiagnosticCoordinate
    heterogeneousOrMixed
    systematicReviewEvidence
    "The systematic review/meta-analysis reports strong methodological and regional heterogeneity; it does not license a general PTSD = low-GABA law."

------------------------------------------------------------------------
-- Existing-repo attachment.
------------------------------------------------------------------------

gabaVocabularyOwner : CandidateOnlyCore.CandidateOnlyRow
gabaVocabularyOwner = Vocabulary.gabaCandidate

gabaVocabularyOwnerRemainsCandidateOnly :
  CandidateOnlyCore.candidateOnly gabaVocabularyOwner ≡ true
gabaVocabularyOwnerRemainsCandidateOnly =
  CandidateOnlyCore.candidateOnlyIsTrue Vocabulary.gabaCandidateReceipt

autismCoordinateOwner : Geometry.NeurotypeCoordinate
autismCoordinateOwner = Geometry.autisticCoordinate

adhdCoordinateOwner : Geometry.NeurotypeCoordinate
adhdCoordinateOwner = Geometry.adhdCoordinate

audhdCoordinateOwner : Geometry.NeurotypeCoordinate
audhdCoordinateOwner = Geometry.audhdCoordinate

------------------------------------------------------------------------
-- Promotion gates.
--
-- Empty permission types encode absence of authority in this module.  They do
-- not assert that such bridges are impossible in nature; they assert only that
-- the cited evidence receipts above do not themselves inhabit the bridge.
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

data SensoryAssociationIsGlobalSeverityLawPermission : Set where

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

sensoryAssociationDoesNotUniversalizeAutism :
  SensoryAssociationIsGlobalSeverityLawPermission → ⊥
sensoryAssociationDoesNotUniversalizeAutism ()

------------------------------------------------------------------------
-- Literal transcript audit.
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
    origin : Source.AttributedSource
    sourceSpan : String
    transcriptClaim : String
    status : AuditStatus
    basis : String

open TranscriptClaimAudit public

transcriptClaimAudits : List TranscriptClaimAudit
transcriptClaimAudits =
  transcriptClaimAudit
    transcriptSource
    "00:00:00,000 --> 00:00:05,620"
    "GABA goes as far as to predict successful thought suppression, not emotional suppression."
    supportedBounded
    "Schmitz et al. 2017 supports the hippocampal-GABA / retrieval-suppression component. Its explicit functional comparison is action stopping, not emotion suppression, so the final contrast is not promoted." ∷
  transcriptClaimAudit
    transcriptSource
    "00:00:13,030 --> 00:00:21,220"
    "GABA is enough to create autism."
    blockedPromotion
    "Group differences and associations do not supply a causal-sufficiency receipt." ∷
  transcriptClaimAudit
    transcriptSource
    "00:00:22,000 --> 00:00:28,020"
    "The GABA pathway is enough to create ADHD."
    blockedPromotion
    "No causal-sufficiency receipt is present; this module deliberately has no general ADHD-low-GABA evidence row." ∷
  transcriptClaimAudit
    transcriptSource
    "00:00:28,340 --> 00:00:38,440"
    "GABA levels in ADHD are lower."
    needsNamedReceipt
    "No general diagnosis-wide ADHD-low-GABA receipt is admitted here." ∷
  transcriptClaimAudit
    transcriptSource
    "00:00:38,440 --> 00:00:45,900"
    "Higher the GABA, lower the ADHD symptom severity."
    needsNamedReceipt
    "Requires a named population, brain region, measurement method, symptom instrument, direction/effect estimate, and source." ∷
  transcriptClaimAudit
    transcriptSource
    "00:01:09,380 --> 00:01:13,460"
    "lack of neurosynchrony means by definition insecure attachment"
    domainBridgeMissing
    "Neural synchrony and attachment status are different empirical domains; no definitional or validated empirical adapter is present." ∷
  transcriptClaimAudit
    transcriptSource
    "00:01:22,930 --> 00:01:26,610"
    "GABA is lower in autism compared to healthy controls."
    candidateAssociationOnly
    "The 2024 meta-analysis supports a group-level lower-GABA direction overall, while preserving regional, demographic, and methodological heterogeneity." ∷
  transcriptClaimAudit
    transcriptSource
    "00:01:26,960 --> 00:01:35,190"
    "Lower GABA is associated with greater sensory sensitivity in autism."
    candidateAssociationOnly
    "Puts et al. 2017 and Umesawa et al. 2020 support bounded regional/task-specific sensory associations; they do not establish a universal whole-brain or global symptom-severity law." ∷ []

------------------------------------------------------------------------
-- Claim-boundary summary.
------------------------------------------------------------------------

record GABAPhenotypeBoundary : Set where
  constructor gabaPhenotypeBoundary
  field
    regionalEvidenceIsRepresentable : Bool
    regionalEvidenceIsRepresentableIsTrue : regionalEvidenceIsRepresentable ≡ true
    canonicalAttributionCoreIsUsed : Bool
    canonicalAttributionCoreIsUsedIsTrue : canonicalAttributionCoreIsUsed ≡ true
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
    sensoryAssociationIsUniversalSeverityLaw : Bool
    sensoryAssociationIsUniversalSeverityLawIsFalse : sensoryAssociationIsUniversalSeverityLaw ≡ false

canonicalGABAPhenotypeBoundary : GABAPhenotypeBoundary
canonicalGABAPhenotypeBoundary =
  gabaPhenotypeBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
