module DASHI.Biology.BraidedEmotionProcessBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Braided emotion process boundary.
--
-- Candidate-only formal carrier for a reconciled emotion ontology.
-- It preserves bodily regulation, predictive interpretation, appraisal,
-- action readiness, conceptual/language mediation, relation, and conscious
-- experience as coupled but non-identical strands.
--
-- This module does not promote a clinical theory, diagnostic ontology,
-- therapeutic protocol, or claim that one disputed emotion theory has won.

------------------------------------------------------------------------
-- The strands of an emotion episode.

data EmotionStrand : Set where
  bodilyRegulationStrand : EmotionStrand
  interoceptiveStrand : EmotionStrand
  predictiveInterpretationStrand : EmotionStrand
  appraisalSignificanceStrand : EmotionStrand
  actionReadinessStrand : EmotionStrand
  conceptLanguageStrand : EmotionStrand
  socialRelationalStrand : EmotionStrand
  consciousExperienceStrand : EmotionStrand

strandName : EmotionStrand → String
strandName bodilyRegulationStrand = "bodily-regulation"
strandName interoceptiveStrand = "interoception"
strandName predictiveInterpretationStrand = "predictive-interpretation"
strandName appraisalSignificanceStrand = "appraisal-significance"
strandName actionReadinessStrand = "action-readiness"
strandName conceptLanguageStrand = "concept-language"
strandName socialRelationalStrand = "social-relational"
strandName consciousExperienceStrand = "conscious-experience"

canonicalEmotionStrands : List EmotionStrand
canonicalEmotionStrands =
  bodilyRegulationStrand
  ∷ interoceptiveStrand
  ∷ predictiveInterpretationStrand
  ∷ appraisalSignificanceStrand
  ∷ actionReadinessStrand
  ∷ conceptLanguageStrand
  ∷ socialRelationalStrand
  ∷ consciousExperienceStrand
  ∷ []

------------------------------------------------------------------------
-- Episode and label carriers.

record EmotionEpisode : Set where
  constructor mkEmotionEpisode
  field
    episodeLabel : String
    episodeStrands : List EmotionStrand
    temporallyExtended : Bool
    organismWorldCoupled : Bool
    historicallyConditioned : Bool
    materiallyConstrained : Bool
    relationallySituated : Bool
    singleStrandReductionClaimed : Bool

open EmotionEpisode public

record EmotionLabel : Set where
  constructor mkEmotionLabel
  field
    labelText : String
    provisional : Bool
    revisable : Bool
    treatedAsEpisodeIdentity : Bool
    canDiscloseStructure : Bool
    canCompressStructure : Bool
    canReshapeEpisode : Bool
    canObscureEpisode : Bool

open EmotionLabel public

canonicalBraidedEpisode : EmotionEpisode
canonicalBraidedEpisode =
  mkEmotionEpisode
    "canonical-braided-emotion-episode"
    canonicalEmotionStrands
    true
    true
    true
    true
    true
    false

canonicalProvisionalLabel : EmotionLabel
canonicalProvisionalLabel =
  mkEmotionLabel
    "candidate-emotion-label"
    true
    true
    false
    true
    true
    true
    true

------------------------------------------------------------------------
-- Non-reduction receipts.

record NonReductionReceipt (episode : EmotionEpisode) : Set where
  constructor mkNonReductionReceipt
  field
    receiptLabel : String
    receiptEpisode : EmotionEpisode
    receiptEpisodeMatches : receiptEpisode ≡ episode
    bodyAloneIsNotEpisode : Bool
    actionReadinessAloneIsNotEpisode : Bool
    conceptAloneIsNotEpisode : Bool
    languageAloneIsNotEpisode : Bool
    consciousReportAloneIsNotEpisode : Bool
    socialRelationAloneIsNotEpisode : Bool
    noSingleStrandReduction : Bool
    noSingleStrandReductionIsTrue : noSingleStrandReduction ≡ true

open NonReductionReceipt public

canonicalNonReductionReceipt :
  NonReductionReceipt canonicalBraidedEpisode
canonicalNonReductionReceipt =
  mkNonReductionReceipt
    "braided-emotion-non-reduction"
    canonicalBraidedEpisode
    refl
    true
    true
    true
    true
    true
    true
    true
    refl

------------------------------------------------------------------------
-- Theory families remain locally useful and globally non-exclusive.

data EmotionTheory : Set where
  basicDiscreteTheory : EmotionTheory
  constructionistTheory : EmotionTheory
  appraisalTheory : EmotionTheory
  actionReadinessTheory : EmotionTheory
  predictiveProcessingTheory : EmotionTheory
  enactiveEcologicalTheory : EmotionTheory
  socialRelationalTheory : EmotionTheory

emotionTheoryName : EmotionTheory → String
emotionTheoryName basicDiscreteTheory = "basic-discrete"
emotionTheoryName constructionistTheory = "constructionist"
emotionTheoryName appraisalTheory = "appraisal"
emotionTheoryName actionReadinessTheory = "action-readiness"
emotionTheoryName predictiveProcessingTheory = "predictive-processing"
emotionTheoryName enactiveEcologicalTheory = "enactive-ecological"
emotionTheoryName socialRelationalTheory = "social-relational"

record TheoryScopeRow : Set where
  constructor mkTheoryScopeRow
  field
    theory : EmotionTheory
    strongestQuestion : String
    preservedInsight : String
    knownBlindSpot : String
    globallyExclusive : Bool

open TheoryScopeRow public

canonicalTheoryRows : List TheoryScopeRow
canonicalTheoryRows =
  mkTheoryScopeRow
    basicDiscreteTheory
    "evolved and recurrent organisation"
    "shared biological regularities"
    "within-category and cultural variation"
    false
  ∷ mkTheoryScopeRow
    constructionistTheory
    "contextual category formation"
    "concept learning and flexible categorisation"
    "biological asymmetries and recurrent function"
    false
  ∷ mkTheoryScopeRow
    appraisalTheory
    "goal-relative significance"
    "agency control norm and relevance structure"
    "preconceptual affect and bodily constraint"
    false
  ∷ mkTheoryScopeRow
    actionReadinessTheory
    "situated behavioural preparation"
    "changes in affordance and action tendency"
    "reflection passivity mixed states and relation"
    false
  ∷ mkTheoryScopeRow
    predictiveProcessingTheory
    "prediction uncertainty and precision"
    "reciprocal inference across body and world"
    "risk of explaining everything without discrimination"
    false
  ∷ mkTheoryScopeRow
    enactiveEcologicalTheory
    "organism-environment coordination"
    "affordances and world-involving process"
    "specific neural and physiological mechanism"
    false
  ∷ mkTheoryScopeRow
    socialRelationalTheory
    "interpersonal and institutional constitution"
    "co-regulation power obligation and history"
    "subpersonal and organismic continuity"
    false
  ∷ []

record ScaleIndexedPluralismReceipt : Set where
  constructor mkScaleIndexedPluralismReceipt
  field
    receiptLabel : String
    theoryRows : List TheoryScopeRow
    localAdequacyAllowed : Bool
    globalReductionRequired : Bool
    disagreementPreserved : Bool
    contentionCollapsed : Bool
    pluralismHolds : Bool
    pluralismHoldsIsTrue : pluralismHolds ≡ true

open ScaleIndexedPluralismReceipt public

canonicalScaleIndexedPluralismReceipt : ScaleIndexedPluralismReceipt
canonicalScaleIndexedPluralismReceipt =
  mkScaleIndexedPluralismReceipt
    "scale-indexed-emotion-theory-pluralism"
    canonicalTheoryRows
    true
    false
    true
    false
    true
    refl

------------------------------------------------------------------------
-- Braided epistemic provenance and obligation.

data KnowledgeRoute : Set where
  neuralExperimentalRoute : KnowledgeRoute
  phenomenologicalRoute : KnowledgeRoute
  relationalRoute : KnowledgeRoute
  culturalNarrativeRoute : KnowledgeRoute
  ethicalObligationRoute : KnowledgeRoute

record KnowledgeStrand : Set where
  constructor mkKnowledgeStrand
  field
    route : KnowledgeRoute
    provenance : String
    method : String
    warrant : String
    purpose : String
    obligation : String
    replaceableByAnotherRoute : Bool

open KnowledgeStrand public

canonicalKnowledgeBraid : List KnowledgeStrand
canonicalKnowledgeBraid =
  mkKnowledgeStrand
    neuralExperimentalRoute
    "experimental and comparative neuroscience"
    "measurement modelling intervention and replication"
    "empirical adequacy and transparent uncertainty"
    "mechanistic and functional explanation"
    "do not promote mechanism into total human meaning"
    false
  ∷ mkKnowledgeStrand
    phenomenologicalRoute
    "first-person situated experience"
    "careful description and revisable report"
    "coherence discrimination and longitudinal fit"
    "render lived structure visible"
    "do not erase the experiencer through third-person compression"
    false
  ∷ mkKnowledgeStrand
    relationalRoute
    "interaction family community and institution"
    "observation testimony dialogue and practice"
    "relational consequence and reciprocal correction"
    "identify co-regulation power and repair"
    "respond to what the relationship requires"
    false
  ∷ mkKnowledgeStrand
    culturalNarrativeRoute
    "language story history land and inherited practice"
    "narrative teaching comparison and accountable transmission"
    "provenance-sensitive continuity and community warrant"
    "preserve meaning that measurement alone does not contain"
    "do not extract concepts while erasing their source"
    false
  ∷ mkKnowledgeStrand
    ethicalObligationRoute
    "consequences of naming and knowing"
    "deliberation consent reciprocity and harm review"
    "responsible action under uncertainty"
    "connect description to care and restraint"
    "knowing creates obligations rather than mere classification"
    false
  ∷ []

record BraidedKnowledgeReceipt : Set where
  constructor mkBraidedKnowledgeReceipt
  field
    receiptLabel : String
    knowledgeStrands : List KnowledgeStrand
    provenancePreserved : Bool
    warrantsRemainDistinct : Bool
    reciprocalConstraintAllowed : Bool
    extractiveFusionBlocked : Bool
    obligationIncluded : Bool
    braidHolds : Bool
    braidHoldsIsTrue : braidHolds ≡ true

open BraidedKnowledgeReceipt public

canonicalBraidedKnowledgeReceipt : BraidedKnowledgeReceipt
canonicalBraidedKnowledgeReceipt =
  mkBraidedKnowledgeReceipt
    "braided-emotion-knowledge-receipt"
    canonicalKnowledgeBraid
    true
    true
    true
    true
    true
    true
    refl

------------------------------------------------------------------------
-- Practical multi-pass observation remains label-capable but label-provisional.

data ObservationPass : Set where
  lowInferenceSensationPass : ObservationPass
  actionTendencyPass : ObservationPass
  appraisalContextPass : ObservationPass
  candidateLabelPass : ObservationPass
  relationalObligationPass : ObservationPass
  chosenActionPass : ObservationPass

canonicalObservationPasses : List ObservationPass
canonicalObservationPasses =
  lowInferenceSensationPass
  ∷ actionTendencyPass
  ∷ appraisalContextPass
  ∷ candidateLabelPass
  ∷ relationalObligationPass
  ∷ chosenActionPass
  ∷ []

record MultiPassPracticeBoundary : Set where
  constructor mkMultiPassPracticeBoundary
  field
    boundaryLabel : String
    passes : List ObservationPass
    labelFirstRequired : Bool
    labelFreeRequired : Bool
    labelsRemainAvailable : Bool
    labelsRemainProvisional : Bool
    actionCanProceedWithoutPerfectClassification : Bool
    clinicalProtocolClaimed : Bool
    boundaryHolds : Bool
    boundaryHoldsIsTrue : boundaryHolds ≡ true

open MultiPassPracticeBoundary public

canonicalMultiPassPracticeBoundary : MultiPassPracticeBoundary
canonicalMultiPassPracticeBoundary =
  mkMultiPassPracticeBoundary
    "neither-label-first-nor-label-free"
    canonicalObservationPasses
    false
    false
    true
    true
    true
    false
    true
    refl

------------------------------------------------------------------------
-- Compact non-promotion surface.

record BraidedEmotionBoundary : Set where
  constructor mkBraidedEmotionBoundary
  field
    episode : EmotionEpisode
    label : EmotionLabel
    nonReduction : NonReductionReceipt episode
    theoryPluralism : ScaleIndexedPluralismReceipt
    knowledgeBraid : BraidedKnowledgeReceipt
    practiceBoundary : MultiPassPracticeBoundary
    emotionIsBiologyAlone : Bool
    emotionIsLanguageAlone : Bool
    emotionIsActionAlone : Bool
    emotionIsPrivateBrainStateAlone : Bool
    emotionIsArbitraryConstruction : Bool
    constrainedConstructionClaim : Bool
    relationalCoordinationClaim : Bool
    clinicalAuthorityClaimed : Bool
    diagnosticAuthorityClaimed : Bool
    therapeuticAuthorityClaimed : Bool

open BraidedEmotionBoundary public

canonicalBraidedEmotionBoundary : BraidedEmotionBoundary
canonicalBraidedEmotionBoundary =
  mkBraidedEmotionBoundary
    canonicalBraidedEpisode
    canonicalProvisionalLabel
    canonicalNonReductionReceipt
    canonicalScaleIndexedPluralismReceipt
    canonicalBraidedKnowledgeReceipt
    canonicalMultiPassPracticeBoundary
    false
    false
    false
    false
    false
    true
    true
    false
    false
    false

braidedEmotionBoundaryStatement : String
braidedEmotionBoundaryStatement =
  "emotion is a constrained construction enacted by embodied organisms in consequential relationships; labels and theories remain useful, revisable, scale-indexed, and non-authoritative"
