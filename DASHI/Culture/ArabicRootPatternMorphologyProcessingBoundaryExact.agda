module DASHI.Culture.ArabicRootPatternMorphologyProcessingBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Culture.LinguisticMorphologySourceObservationBridgeExact as Morphology
import DASHI.Culture.PhonologicalFeatureMatrixContrastExact as Phonology

------------------------------------------------------------------------
-- ARABIC ROOT/PATTERN MORPHOLOGY + PROCESSING BOUNDARY
--
-- Triggering observation:
-- user-supplied social-media transcript, 2026-09-25, describing Arabic
-- consonantal roots, vocalic/templates, unvowelled orthography, and alleged
-- "dual-track" neural processing.
--
-- This owner keeps three things separate:
--   (1) established linguistic architecture of Arabic root/pattern morphology;
--   (2) experimentally observed morphology-sensitive processing effects;
--   (3) stronger reel claims such as a unique cognitive workout, exact
--       simultaneous region splitting, or general mental-agility advantage.
--
-- The third lane is not promoted from the first two.
------------------------------------------------------------------------

rydingRootPatternSource : Attribution.AttributedSource
rydingRootPatternSource = Attribution.mkDOISource
  "Karin C. Ryding"
  "Derivational morphology: the root/pattern system"
  "Arabic: A Linguistic Introduction, Cambridge University Press"
  "2014"
  "10.1017/CBO9781139151016.007"
  "https://doi.org/10.1017/CBO9781139151016.007"
  Attribution.academicChapterSource
  "source anchor for Arabic lexical roots, grammatical patterns, and root/pattern derivation; not authority for DASHI processing claims"
  Attribution.publicAttribution

boudelaaMarslenWilsonNeuralSource : Attribution.AttributedSource
boudelaaMarslenWilsonNeuralSource = Attribution.mkDOISource
  "Sami Boudelaa; William D. Marslen-Wilson"
  "Arabic morphology in the neural language system"
  "Journal of Cognitive Neuroscience"
  "2010"
  "10.1162/jocn.2009.21273"
  "https://doi.org/10.1162/jocn.2009.21273"
  Attribution.academicArticleSource
  "source anchor for experimentally distinct electrophysiological responses to Arabic consonantal roots and vocalic word patterns; not a cognitive-superiority theorem"
  Attribution.publicAttribution

gwilliamsMarantzRootProcessingSource : Attribution.AttributedSource
gwilliamsMarantzRootProcessingSource = Attribution.mkDOISource
  "Laura Gwilliams; Alec Marantz"
  "Non-linear processing of a linear speech stream: The influence of morphological structure on the recognition of spoken Arabic words"
  "Brain and Language"
  "2015"
  "10.1016/j.bandl.2015.04.006"
  "https://doi.org/10.1016/j.bandl.2015.04.006"
  Attribution.academicArticleSource
  "source anchor for MEG evidence that root-sensitive probability predicts neural activity during spoken Arabic recognition; not evidence for a generic mental-agility advantage"
  Attribution.publicAttribution

rydingSourceRoleReceipt :
  AttributionSnowball.SourceRoleSnowballReceipt rydingRootPatternSource
rydingSourceRoleReceipt =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt rydingRootPatternSource

boudelaaSourceRoleReceipt :
  AttributionSnowball.SourceRoleSnowballReceipt boudelaaMarslenWilsonNeuralSource
boudelaaSourceRoleReceipt =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt boudelaaMarslenWilsonNeuralSource

gwilliamsSourceRoleReceipt :
  AttributionSnowball.SourceRoleSnowballReceipt gwilliamsMarantzRootProcessingSource
gwilliamsSourceRoleReceipt =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt gwilliamsMarantzRootProcessingSource

------------------------------------------------------------------------
-- Language-specific morphology receipts.
------------------------------------------------------------------------

data ArabicMorphologicalLayer : Set where
  consonantalRoot
  vocalicPattern
  prosodicTemplate
  affixalMaterial
  surfaceWord
  unresolvedLayer : ArabicMorphologicalLayer

data ArabicOrthographicVowelState : Set where
  fullyDiacritized
  partiallyDiacritized
  undiacritized
  unresolvedVowelState : ArabicOrthographicVowelState

record ArabicRootPatternFormReceipt : Set where
  constructor arabic-root-pattern-form-receipt
  field
    languageOrVariety : String
    rootReference : String
    rootSemanticFieldReference : String
    patternReference : String
    templateReference : String
    affixReference : String
    surfaceForm : String
    transliteration : String
    glossReference : String
    grammaticalFeatureReference : String
    wordClassReference : String
    orthographicVowelState : ArabicOrthographicVowelState
    linguisticSourceReference : String
    analysisRevision : String
    concreteAnalysisPaid : Bool
open ArabicRootPatternFormReceipt public

ktbKatabaReceipt : ArabicRootPatternFormReceipt
ktbKatabaReceipt =
  arabic-root-pattern-form-receipt
    "Modern Standard / Classical Arabic reference form"
    "k-t-b / ك-ت-ب"
    "writing-related lexical family; do not collapse root to one fully specified proposition"
    "Form-I perfective active vocalism"
    "root consonants interdigitated with vocalic/template material"
    "none beyond declared pattern material"
    "كَتَبَ"
    "kataba"
    "write; third-person masculine singular perfective active"
    "perfective; active"
    "verb"
    fullyDiacritized
    "Ryding 2014 root/pattern morphology; surface/gloss cross-check"
    "2026-09-25"
    true

ktbKutibaReceipt : ArabicRootPatternFormReceipt
ktbKutibaReceipt =
  arabic-root-pattern-form-receipt
    "Modern Standard / Classical Arabic reference form"
    "k-t-b / ك-ت-ب"
    "writing-related lexical family; do not collapse root to one fully specified proposition"
    "Form-I perfective passive vocalism"
    "root consonants interdigitated with passive vocalic/template material"
    "none beyond declared pattern material"
    "كُتِبَ"
    "kutiba"
    "was written; third-person masculine singular perfective passive"
    "perfective; passive"
    "verb"
    fullyDiacritized
    "Arabic orthographic/morphological literature; reel transcript corrected from final -h spelling"
    "2026-09-25"
    true

ktbKitabReceipt : ArabicRootPatternFormReceipt
ktbKitabReceipt =
  arabic-root-pattern-form-receipt
    "Modern Standard Arabic reference form"
    "k-t-b / ك-ت-ب"
    "writing-related lexical family"
    "nominal root/pattern derivation"
    "k-i-t-aa-b"
    "long-vowel/template material declared separately from root consonants"
    "كِتَاب"
    "kitāb"
    "book"
    "lexical noun derivation"
    "noun"
    fullyDiacritized
    "Ryding 2014; Arabic lexical cross-check"
    "2026-09-25"
    true

ktbMaktabaReceipt : ArabicRootPatternFormReceipt
ktbMaktabaReceipt =
  arabic-root-pattern-form-receipt
    "Modern Standard Arabic reference form"
    "k-t-b / ك-ت-ب"
    "writing-related lexical family"
    "place/nominal derivational pattern"
    "ma-k-ta-ba"
    "m- prefix plus template/vocalism; not 'm' alone"
    "مَكْتَبَة"
    "maktaba"
    "library / bookstore"
    "derived place/institution noun"
    "noun"
    fullyDiacritized
    "Ryding 2014; Arabic lexical cross-check"
    "2026-09-25"
    true

------------------------------------------------------------------------
-- Undiacritized reading is an ambiguity/reconstruction problem, not a
-- theorem that short vowels alone determine exact meaning.
------------------------------------------------------------------------

record ArabicUndiacritizedResolutionReceipt : Set where
  constructor arabic-undiacritized-resolution-receipt
  field
    consonantalSurfaceReference : String
    candidateReadingLedgerReference : String
    morphologyConstraintReference : String
    syntacticContextReference : String
    semanticContextReference : String
    frequencyOrPriorReference : String
    shortVowelsExplicitlyPresent : Bool
    multipleReadingsPossible : Bool
    contextualResolutionRequired : Bool
    exactResolutionPaid : Bool
open ArabicUndiacritizedResolutionReceipt public

ktbUndiacritizedResolution : ArabicUndiacritizedResolutionReceipt
ktbUndiacritizedResolution =
  arabic-undiacritized-resolution-receipt
    "كتب / ktb-shaped undiacritized orthographic string"
    "e.g. kataba / kutiba / kutub and other context-dependent analyses"
    "root/pattern morphology constrains candidate analyses"
    "sentence-level morphosyntax may disambiguate"
    "lexical/semantic context may disambiguate"
    "form frequency and reader knowledge may contribute"
    false
    true
    true
    false

------------------------------------------------------------------------
-- Processing evidence.  Distinct response profiles are evidence about
-- processing architecture; they do not license the reel's stronger slogan.
------------------------------------------------------------------------

data NeuroMethod : Set where
  EEGMMN
  MEG
  behavioural
  mixedMethod
  unresolvedMethod : NeuroMethod

record ArabicMorphologyProcessingEvidence : Set where
  constructor arabic-morphology-processing-evidence
  field
    sourceReference : String
    method : NeuroMethod
    stimulusDomainReference : String
    rootSensitiveEffectReference : String
    patternSensitiveEffectReference : String
    timingDifferenceReference : String
    topographyOrRegionReference : String
    rootSensitiveEffectPaid : Bool
    patternSensitiveEffectPaid : Bool
    distinctTimingPaid : Bool
    distinctSpatialProfilePaid : Bool
    simultaneousIndependentTracksPaid : Bool
    genericCognitiveWorkoutPaid : Bool
open ArabicMorphologyProcessingEvidence public

boudelaaMMNEvidence : ArabicMorphologyProcessingEvidence
boudelaaMMNEvidence =
  arabic-morphology-processing-evidence
    "Boudelaa and Marslen-Wilson, Journal of Cognitive Neuroscience, DOI 10.1162/jocn.2009.21273"
    EEGMMN
    "Arabic root and vocalic word-pattern manipulations"
    "root-related MMN reported earlier after deviation point"
    "word-pattern-related MMN reported later after deviation point"
    "reported onset difference: root approximately 160 ms; pattern approximately 250 ms"
    "reported topographic difference: root more symmetric fronto-central; pattern more left-lateralized"
    true
    true
    true
    true
    false
    false

gwilliamsMEGEvidence : ArabicMorphologyProcessingEvidence
gwilliamsMEGEvidence =
  arabic-morphology-processing-evidence
    "Gwilliams and Marantz, Brain and Language, DOI 10.1016/j.bandl.2015.04.006"
    MEG
    "spoken Arabic word recognition"
    "root-based lexical probability significantly predicted neural activity"
    "this experiment is not a matched root-versus-pattern two-track decomposition theorem"
    "not the same timing comparison as the MMN experiment"
    "root prediction related to superior temporal activity"
    true
    false
    false
    true
    false
    false

------------------------------------------------------------------------
-- Reuse the generic repo owners rather than replacing them.
------------------------------------------------------------------------

genericMorphologyBoundaryRetained : Morphology.LinguisticMorphologyBoundary
genericMorphologyBoundaryRetained =
  Morphology.canonicalLinguisticMorphologyBoundary

genericPhonologyBoundaryRetained : Phonology.PhonologicalFeatureMatrixBoundary
genericPhonologyBoundaryRetained =
  Phonology.canonicalPhonologicalFeatureMatrixBoundary

record ArabicRootPatternIntegrationBoundary : Set where
  constructor arabic-root-pattern-integration-boundary
  field
    genericMorphologyOwnerReused : Bool
    languageSpecificArabicReceiptsAdded : Bool
    rootPatternInterdigitationRepresented : Bool
    undiacritizedAmbiguityRepresented : Bool
    morphologyAndOrthographySeparated : Bool
    neuralEvidenceSeparatedFromLinguisticArchitecture : Bool
    reelExactDualTrackClaimPromoted : Bool
    reelMentalAgilityClaimPromoted : Bool
    arabicUniquenessClaimPromoted : Bool
open ArabicRootPatternIntegrationBoundary public

canonicalArabicRootPatternIntegrationBoundary :
  ArabicRootPatternIntegrationBoundary
canonicalArabicRootPatternIntegrationBoundary =
  arabic-root-pattern-integration-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls against the strongest unsupported reductions in the transcript.
------------------------------------------------------------------------

data RootEqualsPureAbstractMeaning : Set where
data VowelsAloneDetermineExactMeaning : Set where
data DistinctNeuralResponseCreatesCognitiveSuperiority : Set where
data ArabicRootPatternIsUniqueToArabic : Set where
data UndiacritizedReadingHasOneContextFreeExpansion : Set where
data EEGDifferenceEqualsSimultaneousIndependentRegions : Set where

rootDoesNotEqualFullySpecifiedMeaning :
  RootEqualsPureAbstractMeaning → ⊥
rootDoesNotEqualFullySpecifiedMeaning ()

vowelsAloneDoNotDetermineExactMeaning :
  VowelsAloneDetermineExactMeaning → ⊥
vowelsAloneDoNotDetermineExactMeaning ()

neuralDifferenceDoesNotCreateSuperiority :
  DistinctNeuralResponseCreatesCognitiveSuperiority → ⊥
neuralDifferenceDoesNotCreateSuperiority ()

rootPatternNotUniqueToArabic :
  ArabicRootPatternIsUniqueToArabic → ⊥
rootPatternNotUniqueToArabic ()

undiacritizedFormNeedNotHaveUniqueContextFreeReading :
  UndiacritizedReadingHasOneContextFreeExpansion → ⊥
undiacritizedFormNeedNotHaveUniqueContextFreeReading ()

eegDifferenceDoesNotProveReelArchitecture :
  EEGDifferenceEqualsSimultaneousIndependentRegions → ⊥
eegDifferenceDoesNotProveReelArchitecture ()

record ReelClaimAudit : Set where
  constructor reel-claim-audit
  field
    nonConcatenativeRootPatternCoreSupported : Bool
    ktbDerivationalFamilySupported : Bool
    ordinaryTextOftenOmitsShortVowelDiacriticsSupported : Bool
    morphologyAndContextAidRecoverySupported : Bool
    morphologySensitiveNeuralEffectsSupported : Bool
    exactTwoIndependentRegionsSimultaneouslySupported : Bool
    builtInMentalAgilityAdvantageSupported : Bool
    arabicIsUniqueInHavingRootPatternMorphologySupported : Bool
open ReelClaimAudit public

canonicalReelClaimAudit : ReelClaimAudit
canonicalReelClaimAudit =
  reel-claim-audit
    true
    true
    true
    true
    true
    false
    false
    false
