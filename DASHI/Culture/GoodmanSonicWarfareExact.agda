module DASHI.Culture.GoodmanSonicWarfareExact where

------------------------------------------------------------------------
-- GOODMAN / SONIC WARFARE / SOURCE-TYPED NON-PROMOTION
--
-- Primary source: Steve Goodman, Sonic Warfare: Sound, Affect, and the
-- Ecology of Fear, MIT Press, print copyright 2010, publisher's electronic
-- release 2009, DOI 10.7551/mitpress/7999.001.0001.
-- ISBN 9780262013475; 9780262258838 (electronic).
-- https://doi.org/10.7551/mitpress/7999.001.0001
--
-- Goodman's conceptual synthesis and its historical, political, artistic,
-- and speculative accounts are attributed to Goodman and his named
-- predecessors. All finite counterexamples and type distinctions here are
-- DASHI constructions. Neither citation nor a passing Agda proof provides
-- an empirical acoustic, medical, historical, or causal result.
--
-- P0: The word "mirror" cannot identify acoustic reflection, an echo,
-- a figurative mirror, or the separately alleged Kozyrev apparatus effect.
-- In particular, do not import open PR #1404 as merged source authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.ObserverConditionedTransportBridge as Transport
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Closure.SensoryAttractorClasses as Sensory
import DASHI.Biology.BioacousticMultimodalLagFactorisationExact as Lag
import DASHI.Biology.BraidedEmotionEvidenceRegistry as Emotion
import DASHI.Biology.AnimalCommunicationPassiveAcousticLocalizationExact as Localize
import DASHI.Cognition.PNF.ContinuousOscillatorSyntheticReceipt as Osc
import DASHI.Culture.CohnTechnostrategicDiscourseExact as Cohn
import DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact as Philosophy
import DASHI.Culture.GoodmanSonicWarfareRhythmInterventionExact as RhythmCausality
import DASHI.Culture.GoodmanSonicWarfareTransportExact as SoundTransport
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Wikimedia.IbrahimSnowballSkepticismExpertiseTrustPropagandaBidiExact as IbrahimTrust

goodmanSource : Attr.AttributedSource
goodmanSource = Attr.mkDOISource
  "Steve Goodman"
  "Sonic Warfare: Sound, Affect, and the Ecology of Fear"
  "MIT Press, Technologies of Lived Abstraction; print copyright 2010; electronic publication 2009"
  "2009/2010"
  "10.7551/mitpress/7999.001.0001"
  "https://doi.org/10.7551/mitpress/7999.001.0001"
  Attr.academicBookSource
  "Source of cultural and philosophical claims; not source of DASHI finite proofs or calibrated physiological exposure thresholds"
  Attr.publicAttribution

goodmanSources : Attr.AttributedSourceAtlas
goodmanSources = Attr.mkSourceAtlas
  "Goodman Sonic Warfare"
  "Steve Goodman, MIT Press; DASHI application reconstruction"
  (goodmanSource ∷ [])
  "34 numbered chapters, including chapter 34 conclusion; all indexed below and in Docs/papers/GoodmanSonicWarfare.md"

sourceCitationDoesNotPromote :
  (validation : String) →
  Receipt.promotesClaim
    (Attr.attributedSourceAtlasReceipt goodmanSources validation) ≡ false
sourceCitationDoesNotPromote validation =
  Attr.attributedSourceAtlasReceiptNonPromoting goodmanSources validation

------------------------------------------------------------------------
-- PARETO / SNOWBALL SOURCE ROLE: THIS GOODMAN INSTANCE IS REUSED, NOT
-- REDEFINED. The source kind and its proof-nonimport flag survive
-- provenance traversal. A citation does not turn an example into evidence.
------------------------------------------------------------------------

goodmanSnowballRole : Snowball.SourceRoleSnowballReceipt goodmanSource
goodmanSnowballRole = Snowball.canonicalSourceRoleSnowballReceipt goodmanSource

goodmanSourceKindRetained :
  Snowball.sourceKindRetained goodmanSnowballRole ≡ true
goodmanSourceKindRetained = refl

goodmanCitationDoesNotImportProof :
  Snowball.proofNonImportRetained goodmanSnowballRole ≡ true
goodmanCitationDoesNotImportProof = refl

goodmanCitationDoesNotCreateAuthority :
  Snowball.authorityNonCreationRetained goodmanSnowballRole ≡ true
goodmanCitationDoesNotCreateAuthority = refl


------------------------------------------------------------------------
-- INDEPENDENT EMPIRICAL AND STANDARD SOURCES (NOT GOODMAN'S RESULTS)
--
-- Each source has its own original author/date/role. These references
-- inform the proposed soundscape measurement lane. They are not proofs of
-- the Goodman finite model, nor do pooled associations supply individual
-- causal or clinical authority. ISO text is NOT copied here.
------------------------------------------------------------------------

zhangContextReview2025 : Attr.AttributedSource
zhangContextReview2025 = Attr.mkDOISource
  "Ruining Zhang; Hui Ma; Chao Wang; Yuan Zhang; Jian Kang"
  "Soundscape and its context: A framework based on a systematic review"
  "Journal of the Acoustical Society of America 157, 4417-4436"
  "2025"
  "10.1121/10.0036882"
  "https://doi.org/10.1121/10.0036882"
  Attr.academicArticleSource
  "14 theoretical and 52 empirical papers reviewed; source context taxonomy, not a proof of a DASHI response function"
  Attr.publicAttribution

guoUrbanSoundscape2026 : Attr.AttributedSource
guoUrbanSoundscape2026 = Attr.mkDOISource
  "Xuan Guo; Stefan Schmidt; Zhu Chen; Ling Yang; Jiang Liu; Christian Albert"
  "Beyond noise and silence: urban soundscapes and their contribution to human well-being - a systematic review and meta-analysis"
  "npj Urban Sustainability 6, article 130; 17 October 2026"
  "2026"
  "10.1038/s42949-026-00482-2"
  "https://doi.org/10.1038/s42949-026-00482-2"
  Attr.academicArticleSource
  "194-review-study and 66-meta-analysis-study synthesis; heterogeneous associations and context moderators, not a universal sound intervention theorem"
  Attr.publicAttribution

isoNonAcousticContext2025 : Attr.AttributedSource
isoNonAcousticContext2025 = Attr.mkNoDOISource
  "ISO/TC 43/SC 1"
  "ISO/TS 16755-1:2025 - Non-acoustic factors, Part 1"
  "International Organization for Standardization; first edition, May 2025"
  "2025"
  "https://www.iso.org/standard/84809.html"
  Attr.technicalStandardSource
  "Non-acoustic factor definitions and categorisation; neither an applied human study nor an Agda theorem"
  Attr.publicAttribution

isoSoundscapeAnalysis2025 : Attr.AttributedSource
isoSoundscapeAnalysis2025 = Attr.mkNoDOISource
  "ISO/TC 43/SC 1"
  "ISO/TS 12913-3:2025 - Soundscape, Part 3: Data analysis"
  "International Organization for Standardization; second edition, May 2025"
  "2025"
  "https://www.iso.org/standard/86955.html"
  Attr.technicalStandardSource
  "Standards provenance for in-situ soundscape analysis; successor to 2019 edition, not clinical or causal proof"
  Attr.publicAttribution

soundscapeComparatorSources : Attr.AttributedSourceAtlas
soundscapeComparatorSources = Attr.mkSourceAtlas
  "2025-2026 independent soundscape comparison sources"
  "Original review authors and ISO; DASHI citation/provenance only"
  (zhangContextReview2025 ∷
   guoUrbanSoundscape2026 ∷
   isoNonAcousticContext2025 ∷
   isoSoundscapeAnalysis2025 ∷ [])
  "Independently authored sources for context and measurement design; not proof of Sonic Warfare or a novel force"

soundscapeComparatorsCannotPromote :
  (validation : String) →
  Receipt.promotesClaim
    (Attr.attributedSourceAtlasReceipt soundscapeComparatorSources validation)
  ≡ false
soundscapeComparatorsCannotPromote validation =
  Attr.attributedSourceAtlasReceiptNonPromoting
    soundscapeComparatorSources validation

------------------------------------------------------------------------
-- Claim families and provenance; labels are NOT observations or causes.
------------------------------------------------------------------------

data SonicTheme : Set where
  historicalSonicForce : SonicTheme
  deceptionAndInstitutionalPower : SonicTheme
  physicalVibrationalCarrier : SonicTheme
  rhythmAndTemporalOrganisation : SonicTheme
  embodiedAffectAndFear : SonicTheme
  culturalRepetitionAndDub : SonicTheme
  disseminationAndTransmission : SonicTheme
  artificialAgencyAndBranding : SonicTheme
  unsoundAndVirtualPossibility : SonicTheme
  speculativeFuture : SonicTheme

data ClaimStatus : Set where
  sourcePhilosophical : ClaimStatus
  sourceHistoricalRequiresIndependentRecord : ClaimStatus
  empiricalCandidate : ClaimStatus
  aestheticCulturalInterpretation : ClaimStatus
  fictionalOrSpeculative : ClaimStatus
  dashIFiniteExample : ClaimStatus

record SonicClaim : Set where
  constructor sonic-claim
  field
    label : String
    printedPageOrChapter : String
    theme : SonicTheme
    status : ClaimStatus
    distinctRequiredEvidence : String
    mechanismOrInterpretation : String
    externallyEstablishedHere : Bool
    externallyEstablishedHereIsFalse : externallyEstablishedHere ≡ false

open SonicClaim public

mkCandidate : String → String → SonicTheme → ClaimStatus →
  String → String → SonicClaim
mkCandidate label location theme status evidence interpretation =
  sonic-claim label location theme status evidence interpretation false refl

claims : List SonicClaim
claims =
  mkCandidate "sonic domination and intimidation" "chapters 1-11, pp. 1-62"
    historicalSonicForce sourceHistoricalRequiresIndependentRecord
    "dated archival events, apparatus, provenance, deployment evidence"
    "Goodman examples require case-by-case verification"
  ∷ mkCandidate "vibrational force and mediation" "chapters 12-15, pp. 63-84"
    physicalVibrationalCarrier sourcePhilosophical
    "separate physical wave model, calibrated field and coupling"
    "ontology is not a measured constitutive law"
  ∷ mkCandidate "rhythmanalysis and speed" "chapters 16-20, pp. 85-108"
    rhythmAndTemporalOrganisation sourcePhilosophical
    "measured clock, phase, temporal series and alternative controls"
    "Pinheiro dos Santos, Bachelard, Lefebvre and Goodman retain separate priority"
  ∷ mkCandidate "crowds and affect" "chapters 18-22, pp. 95-116"
    embodiedAffectAndFear empiricalCandidate
    "matched exposure, receiver and contextual covariates"
    "physiological response does not uniquely identify subjective fear"
  ∷ mkCandidate "virtual vibrations and artificial agencies"
    "chapters 23-24, pp. 117-128"
    artificialAgencyAndBranding sourcePhilosophical
    "explicit human/device agency and source claims"
    "agency metaphor does not establish physical autonomy"
  ∷ mkCandidate "schizophonia and circulation" "chapters 25-28, pp. 129-154"
    disseminationAndTransmission aestheticCulturalInterpretation
    "track identifiable recordings, remix lineage, platform and audience"
    "copying sound does not imply copying response"
  ∷ mkCandidate "dub virology and contagious orality" "chapters 29-32, pp. 155-182"
    culturalRepetitionAndDub aestheticCulturalInterpretation
    "source-owned artist, genre and Black Atlantic genealogy"
    "cultural transmission is not literal biological infection"
  ∷ mkCandidate "holosonic control" "chapter 33, pp. 183-188"
    speculativeFuture fictionalOrSpeculative
    "independent demonstration before any technical feasibility assertion"
    "2039 is an internal fictional chapter marker"
  ∷ mkCandidate "unsound" "conclusion, pp. 189-194"
    unsoundAndVirtualPossibility sourcePhilosophical
    "distinguish masked, inaudible, tactile and not-yet-realised possibilities"
    "a philosophical virtual possibility is not a detected signal"
  ∷ []

------------------------------------------------------------------------
-- EXHAUSTIVE SOURCE-INDEXED CHAPTER CONSUMER (34 NUMBERED CHAPTERS)
--
-- The source's final chapter is its conclusion, not an additional 35th
-- chapter. Each constructor selects exactly one printed chapter. Total
-- coverage is a finite registry; it does NOT certify every claim in that
-- chapter or promote a fictional chapter-date to a historical event.
------------------------------------------------------------------------

data SonicChapter : Set where
  chapter01 : SonicChapter
  chapter02 : SonicChapter
  chapter03 : SonicChapter
  chapter04 : SonicChapter
  chapter05 : SonicChapter
  chapter06 : SonicChapter
  chapter07 : SonicChapter
  chapter08 : SonicChapter
  chapter09 : SonicChapter
  chapter10 : SonicChapter
  chapter11 : SonicChapter
  chapter12 : SonicChapter
  chapter13 : SonicChapter
  chapter14 : SonicChapter
  chapter15 : SonicChapter
  chapter16 : SonicChapter
  chapter17 : SonicChapter
  chapter18 : SonicChapter
  chapter19 : SonicChapter
  chapter20 : SonicChapter
  chapter21 : SonicChapter
  chapter22 : SonicChapter
  chapter23 : SonicChapter
  chapter24 : SonicChapter
  chapter25 : SonicChapter
  chapter26 : SonicChapter
  chapter27 : SonicChapter
  chapter28 : SonicChapter
  chapter29 : SonicChapter
  chapter30 : SonicChapter
  chapter31 : SonicChapter
  chapter32 : SonicChapter
  chapter33 : SonicChapter
  chapter34 : SonicChapter

allSonicChapters : List SonicChapter
allSonicChapters =
  chapter01 ∷
  chapter02 ∷
  chapter03 ∷
  chapter04 ∷
  chapter05 ∷
  chapter06 ∷
  chapter07 ∷
  chapter08 ∷
  chapter09 ∷
  chapter10 ∷
  chapter11 ∷
  chapter12 ∷
  chapter13 ∷
  chapter14 ∷
  chapter15 ∷
  chapter16 ∷
  chapter17 ∷
  chapter18 ∷
  chapter19 ∷
  chapter20 ∷
  chapter21 ∷
  chapter22 ∷
  chapter23 ∷
  chapter24 ∷
  chapter25 ∷
  chapter26 ∷
  chapter27 ∷
  chapter28 ∷
  chapter29 ∷
  chapter30 ∷
  chapter31 ∷
  chapter32 ∷
  chapter33 ∷
  chapter34 ∷
  []

chapterPrintedPage : SonicChapter → Nat
chapterPrintedPage chapter01 = 1
chapterPrintedPage chapter02 = 5
chapterPrintedPage chapter03 = 15
chapterPrintedPage chapter04 = 27
chapterPrintedPage chapter05 = 31
chapterPrintedPage chapter06 = 35
chapterPrintedPage chapter07 = 41
chapterPrintedPage chapter08 = 45
chapterPrintedPage chapter09 = 49
chapterPrintedPage chapter10 = 55
chapterPrintedPage chapter11 = 59
chapterPrintedPage chapter12 = 63
chapterPrintedPage chapter13 = 69
chapterPrintedPage chapter14 = 75
chapterPrintedPage chapter15 = 81
chapterPrintedPage chapter16 = 85
chapterPrintedPage chapter17 = 91
chapterPrintedPage chapter18 = 95
chapterPrintedPage chapter19 = 99
chapterPrintedPage chapter20 = 105
chapterPrintedPage chapter21 = 109
chapterPrintedPage chapter22 = 113
chapterPrintedPage chapter23 = 117
chapterPrintedPage chapter24 = 123
chapterPrintedPage chapter25 = 129
chapterPrintedPage chapter26 = 133
chapterPrintedPage chapter27 = 141
chapterPrintedPage chapter28 = 149
chapterPrintedPage chapter29 = 155
chapterPrintedPage chapter30 = 163
chapterPrintedPage chapter31 = 171
chapterPrintedPage chapter32 = 177
chapterPrintedPage chapter33 = 183
chapterPrintedPage chapter34 = 189

chapterTitle : SonicChapter → String
chapterTitle chapter01 = "1998: A Conceptual Event"
chapterTitle chapter02 = "2001: What Is Sonic Warfare?"
chapterTitle chapter03 = "2400-1400 BC: Project Jericho"
chapterTitle chapter04 = "1946: Sonic Dominance"
chapterTitle chapter05 = "1933: Abusing the Military-Entertainment Complex"
chapterTitle chapter06 = "403-221 BC: The Logistics of Deception"
chapterTitle chapter07 = "1944: The Ghost Army"
chapterTitle chapter08 = "1842: Sonic Effects"
chapterTitle chapter09 = "1977: A Sense of the Future"
chapterTitle chapter10 = "1913: The Art of War in the Art of Noise"
chapterTitle chapter11 = "1989: Apocalypse Then"
chapterTitle chapter12 = "1738: Bad Vibrations"
chapterTitle chapter13 = "1884: Dark Precursor"
chapterTitle chapter14 = "1999: Vibrational Anarchitecture"
chapterTitle chapter15 = "13.7 Billion BC: The Ontology of Vibrational Force"
chapterTitle chapter16 = "1931: Rhythmanalysis"
chapterTitle chapter17 = "1900: The Vibrational Nexus"
chapterTitle chapter18 = "1929: Throbs of Experience"
chapterTitle chapter19 = "1677: Ecology of Speeds"
chapterTitle chapter20 = "99-50 BC: Rhythm out of Noise"
chapterTitle chapter21 = "1992: The Throbbing Crowd"
chapterTitle chapter22 = "1993: Vorticist Rhythmachines"
chapterTitle chapter23 = "1946: Virtual Vibrations"
chapterTitle chapter24 = "2012: Artificial Acoustic Agencies"
chapterTitle chapter25 = "1877: Capitalism and Schizophonia"
chapterTitle chapter26 = "1976: Outbreak"
chapterTitle chapter27 = "1971: The Earworm"
chapterTitle chapter28 = "2025: Deja Entendu"
chapterTitle chapter29 = "1985: Dub Virology"
chapterTitle chapter30 = "1928: Contagious Orality"
chapterTitle chapter31 = "2020: Planet of Drums"
chapterTitle chapter32 = "2003: Contagious Transmission"
chapterTitle chapter33 = "2039: Holosonic Control"
chapterTitle chapter34 = "Conclusion: Unsound - The (Sub)Politics of Frequency"

chapterTheme : SonicChapter → SonicTheme
chapterTheme chapter01 = historicalSonicForce
chapterTheme chapter02 = historicalSonicForce
chapterTheme chapter03 = historicalSonicForce
chapterTheme chapter04 = historicalSonicForce
chapterTheme chapter05 = deceptionAndInstitutionalPower
chapterTheme chapter06 = deceptionAndInstitutionalPower
chapterTheme chapter07 = deceptionAndInstitutionalPower
chapterTheme chapter08 = physicalVibrationalCarrier
chapterTheme chapter09 = embodiedAffectAndFear
chapterTheme chapter10 = culturalRepetitionAndDub
chapterTheme chapter11 = culturalRepetitionAndDub
chapterTheme chapter12 = physicalVibrationalCarrier
chapterTheme chapter13 = physicalVibrationalCarrier
chapterTheme chapter14 = physicalVibrationalCarrier
chapterTheme chapter15 = physicalVibrationalCarrier
chapterTheme chapter16 = rhythmAndTemporalOrganisation
chapterTheme chapter17 = rhythmAndTemporalOrganisation
chapterTheme chapter18 = embodiedAffectAndFear
chapterTheme chapter19 = rhythmAndTemporalOrganisation
chapterTheme chapter20 = rhythmAndTemporalOrganisation
chapterTheme chapter21 = embodiedAffectAndFear
chapterTheme chapter22 = culturalRepetitionAndDub
chapterTheme chapter23 = unsoundAndVirtualPossibility
chapterTheme chapter24 = artificialAgencyAndBranding
chapterTheme chapter25 = deceptionAndInstitutionalPower
chapterTheme chapter26 = disseminationAndTransmission
chapterTheme chapter27 = embodiedAffectAndFear
chapterTheme chapter28 = unsoundAndVirtualPossibility
chapterTheme chapter29 = culturalRepetitionAndDub
chapterTheme chapter30 = disseminationAndTransmission
chapterTheme chapter31 = rhythmAndTemporalOrganisation
chapterTheme chapter32 = disseminationAndTransmission
chapterTheme chapter33 = speculativeFuture
chapterTheme chapter34 = unsoundAndVirtualPossibility

chapterStatus : SonicChapter → ClaimStatus
chapterStatus chapter01 = sourcePhilosophical
chapterStatus chapter02 = sourcePhilosophical
chapterStatus chapter03 = sourceHistoricalRequiresIndependentRecord
chapterStatus chapter04 = sourceHistoricalRequiresIndependentRecord
chapterStatus chapter05 = sourceHistoricalRequiresIndependentRecord
chapterStatus chapter06 = sourceHistoricalRequiresIndependentRecord
chapterStatus chapter07 = sourceHistoricalRequiresIndependentRecord
chapterStatus chapter08 = sourcePhilosophical
chapterStatus chapter09 = sourcePhilosophical
chapterStatus chapter10 = aestheticCulturalInterpretation
chapterStatus chapter11 = aestheticCulturalInterpretation
chapterStatus chapter12 = sourcePhilosophical
chapterStatus chapter13 = sourcePhilosophical
chapterStatus chapter14 = sourcePhilosophical
chapterStatus chapter15 = sourcePhilosophical
chapterStatus chapter16 = sourcePhilosophical
chapterStatus chapter17 = sourcePhilosophical
chapterStatus chapter18 = sourcePhilosophical
chapterStatus chapter19 = sourcePhilosophical
chapterStatus chapter20 = sourcePhilosophical
chapterStatus chapter21 = empiricalCandidate
chapterStatus chapter22 = aestheticCulturalInterpretation
chapterStatus chapter23 = sourcePhilosophical
chapterStatus chapter24 = fictionalOrSpeculative
chapterStatus chapter25 = sourcePhilosophical
chapterStatus chapter26 = aestheticCulturalInterpretation
chapterStatus chapter27 = empiricalCandidate
chapterStatus chapter28 = fictionalOrSpeculative
chapterStatus chapter29 = aestheticCulturalInterpretation
chapterStatus chapter30 = aestheticCulturalInterpretation
chapterStatus chapter31 = fictionalOrSpeculative
chapterStatus chapter32 = aestheticCulturalInterpretation
chapterStatus chapter33 = fictionalOrSpeculative
chapterStatus chapter34 = sourcePhilosophical

evidenceFor : ClaimStatus → String
evidenceFor sourceHistoricalRequiresIndependentRecord = "Independent archive and event-specific provenance required"
evidenceFor empiricalCandidate = "Instrument, preregistered question, confounders and independent replication required"
evidenceFor fictionalOrSpeculative = "No real-world event or mechanism inferred from the source's dated scenario"
evidenceFor aestheticCulturalInterpretation = "Preserve original musicians, writers, circulation lineage and context"
evidenceFor sourcePhilosophical = "Source-bound argument; do not treat as physical or clinical measurement"
evidenceFor dashIFiniteExample = "Constructive DASHI example, not human or historical validation"

indexedChapterClaim : SonicChapter → SonicClaim
indexedChapterClaim chapter = mkCandidate
  (chapterTitle chapter)
  "Source chapter, with exact printed start page in chapterPrintedPage"
  (chapterTheme chapter)
  (chapterStatus chapter)
  (evidenceFor (chapterStatus chapter))
  "Source-index fixture only; no independent physical, clinical, causal, historical or Monster-object authority"

------------------------------------------------------------------------
-- P0 mirror: a surface label cannot establish its underlying referent.
-- Goodman chapter 29 (printed pp. 159-160) describes dub echo/delay/
-- reverberation and simulated physical reflections. That source observation
-- is distinct from calibrated acoustic reflection and from a claimed
-- Kozyrev mechanism. This finite example establishes only label ambiguity.
------------------------------------------------------------------------

data MirrorReferent : Set where
  acousticReflection : MirrorReferent
  recordedEcho : MirrorReferent
  figurativeMirror : MirrorReferent
  kozyrevMirrorClaim : MirrorReferent

data MirrorObservation : Set where
  sameMirrorWord : MirrorObservation

data MirrorQuery : Set where
  mirrorNameQuery : MirrorQuery
  mechanismQuery : MirrorQuery

data MirrorAnswer : Set where
  mirrorWordAnswer : MirrorAnswer
  conventionalAcousticAnswer : MirrorAnswer
  notEstablishedMechanismAnswer : MirrorAnswer

mirrorProjection : MirrorReferent → MirrorObservation
mirrorProjection _ = sameMirrorWord

mirrorAnswer : MirrorQuery → MirrorReferent → MirrorAnswer
mirrorAnswer mirrorNameQuery _ = mirrorWordAnswer
mirrorAnswer mechanismQuery acousticReflection = conventionalAcousticAnswer
mirrorAnswer mechanismQuery recordedEcho = conventionalAcousticAnswer
mirrorAnswer mechanismQuery figurativeMirror = notEstablishedMechanismAnswer
mirrorAnswer mechanismQuery kozyrevMirrorClaim = notEstablishedMechanismAnswer

mirrorSemantics : Query.QuerySemantics MirrorReferent MirrorQuery MirrorAnswer
mirrorSemantics = Query.querySemantics mirrorAnswer

mirrorNameAdequate :
  Query.AdequateFor mirrorProjection mirrorSemantics mirrorNameQuery
mirrorNameAdequate =
  Query.factorsForQuery
    {project = mirrorProjection}
    {semantics = mirrorSemantics}
    {query = mirrorNameQuery}
    (λ _ → mirrorWordAnswer)
    (λ _ → refl)

mirrorMechanismCollision :
  Query.QueryAdequacyDefect mirrorProjection mirrorSemantics mechanismQuery
mirrorMechanismCollision =
  Query.queryAdequacyDefect
    {project = mirrorProjection}
    {semantics = mirrorSemantics}
    {query = mechanismQuery}
    acousticReflection kozyrevMirrorClaim refl (λ ())

mirrorNameDoesNotDetermineMechanism :
  Query.AdequateFor mirrorProjection mirrorSemantics mechanismQuery → ⊥
mirrorNameDoesNotDetermineMechanism =
  Query.queryAdequacyDefectBlocksFactorisation mirrorMechanismCollision

acousticMirrorIsNotKozyrevReferent :
  acousticReflection ≡ kozyrevMirrorClaim → ⊥
acousticMirrorIsNotKozyrevReferent ()

------------------------------------------------------------------------
-- Affect non-factorability: equal selected acoustic measurement can coexist
-- with different contexts and responses. This is a finite countermodel,
-- NOT an empirical conclusion about listeners or health outcomes.
------------------------------------------------------------------------

data Encounter : Set where
  sameSoundLowResponse : Encounter
  sameSoundHighResponse : Encounter

data MeasuredAcousticSurface : Set where
  sameSelectedFeatures : MeasuredAcousticSurface

data EncounterQuery : Set where
  acousticFeatureQuery : EncounterQuery
  responseQuery : EncounterQuery

data EncounterAnswer : Set where
  acousticFeatureAnswer : EncounterAnswer
  lowResponseAnswer : EncounterAnswer
  highResponseAnswer : EncounterAnswer

acousticFeatures : Encounter → MeasuredAcousticSurface
acousticFeatures _ = sameSelectedFeatures

encounterAnswer : EncounterQuery → Encounter → EncounterAnswer
encounterAnswer acousticFeatureQuery _ = acousticFeatureAnswer
encounterAnswer responseQuery sameSoundLowResponse = lowResponseAnswer
encounterAnswer responseQuery sameSoundHighResponse = highResponseAnswer

encounterSemantics :
  Query.QuerySemantics Encounter EncounterQuery EncounterAnswer
encounterSemantics = Query.querySemantics encounterAnswer

acousticFeaturesAdequateForFeatureQuery :
  Query.AdequateFor acousticFeatures encounterSemantics acousticFeatureQuery
acousticFeaturesAdequateForFeatureQuery =
  Query.factorsForQuery
    {project = acousticFeatures}
    {semantics = encounterSemantics}
    {query = acousticFeatureQuery}
    (λ _ → acousticFeatureAnswer)
    (λ _ → refl)

responseProjectionDefect :
  Query.QueryAdequacyDefect acousticFeatures encounterSemantics responseQuery
responseProjectionDefect =
  Query.queryAdequacyDefect
    {project = acousticFeatures}
    {semantics = encounterSemantics}
    {query = responseQuery}
    sameSoundLowResponse sameSoundHighResponse refl (λ ())

acousticFeaturesDoNotDetermineEveryResponse :
  Query.AdequateFor acousticFeatures encounterSemantics responseQuery → ⊥
acousticFeaturesDoNotDetermineEveryResponse =
  Query.queryAdequacyDefectBlocksFactorisation responseProjectionDefect


------------------------------------------------------------------------
-- FINITE CONTEXT REFINEMENT / M1
--
-- New DASHI finite witness.  A two-coordinate observation can be adequate
-- for a response query even when neither coordinate alone is adequate.
-- The four world states and their answers are synthetic and deliberately
-- model a Boolean interaction.  A receiver/context label here is not a
-- measured psychological variable or a result about physical humans.
--
-- Reuses the original query-indexed Blackwell-inspired / non-factorability
-- calculus.  It does not redefine information ordering or causality.
------------------------------------------------------------------------

data SignalContextWorld : Set where
  quietProtected : SignalContextWorld
  quietExposed : SignalContextWorld
  loudProtected : SignalContextWorld
  loudExposed : SignalContextWorld

data SignalObservation : Set where
  quietSignal : SignalObservation
  loudSignal : SignalObservation

data ContextObservation : Set where
  protectedContext : ContextObservation
  exposedContext : ContextObservation

data JointObservation : Set where
  quietProtectedObservation : JointObservation
  quietExposedObservation : JointObservation
  loudProtectedObservation : JointObservation
  loudExposedObservation : JointObservation

data ContextualQuery : Set where
  responseFromWorldQuery : ContextualQuery

data ContextualAnswer : Set where
  baselineResponse : ContextualAnswer
  elevatedResponse : ContextualAnswer

signalOnly : SignalContextWorld → SignalObservation
signalOnly quietProtected = quietSignal
signalOnly quietExposed = quietSignal
signalOnly loudProtected = loudSignal
signalOnly loudExposed = loudSignal

contextOnly : SignalContextWorld → ContextObservation
contextOnly quietProtected = protectedContext
contextOnly quietExposed = exposedContext
contextOnly loudProtected = protectedContext
contextOnly loudExposed = exposedContext

jointSignalContext : SignalContextWorld → JointObservation
jointSignalContext quietProtected = quietProtectedObservation
jointSignalContext quietExposed = quietExposedObservation
jointSignalContext loudProtected = loudProtectedObservation
jointSignalContext loudExposed = loudExposedObservation

contextualResponse : SignalContextWorld → ContextualAnswer
contextualResponse quietProtected = baselineResponse
contextualResponse quietExposed = baselineResponse
contextualResponse loudProtected = baselineResponse
contextualResponse loudExposed = elevatedResponse

jointResponse : JointObservation → ContextualAnswer
jointResponse quietProtectedObservation = baselineResponse
jointResponse quietExposedObservation = baselineResponse
jointResponse loudProtectedObservation = baselineResponse
jointResponse loudExposedObservation = elevatedResponse

contextualAnswer : ContextualQuery → SignalContextWorld → ContextualAnswer
contextualAnswer responseFromWorldQuery world = contextualResponse world

contextualSemantics :
  Query.QuerySemantics SignalContextWorld ContextualQuery ContextualAnswer
contextualSemantics = Query.querySemantics contextualAnswer

signalResponseDefect :
  Query.QueryAdequacyDefect
    signalOnly contextualSemantics responseFromWorldQuery
signalResponseDefect =
  Query.queryAdequacyDefect
    loudProtected loudExposed refl (λ ())

contextResponseDefect :
  Query.QueryAdequacyDefect
    contextOnly contextualSemantics responseFromWorldQuery
contextResponseDefect =
  Query.queryAdequacyDefect
    quietExposed loudExposed refl (λ ())

signalAloneCannotDetermineContextualResponse :
  Query.AdequateFor
    signalOnly contextualSemantics responseFromWorldQuery → ⊥
signalAloneCannotDetermineContextualResponse =
  Query.queryAdequacyDefectBlocksFactorisation signalResponseDefect

contextAloneCannotDetermineContextualResponse :
  Query.AdequateFor
    contextOnly contextualSemantics responseFromWorldQuery → ⊥
contextAloneCannotDetermineContextualResponse =
  Query.queryAdequacyDefectBlocksFactorisation contextResponseDefect

jointSignalContextDeterminesSyntheticResponse :
  Query.AdequateFor
    jointSignalContext contextualSemantics responseFromWorldQuery
jointSignalContextDeterminesSyntheticResponse =
  Query.factorsForQuery
    {project = jointSignalContext}
    {semantics = contextualSemantics}
    {query = responseFromWorldQuery}
    jointResponse
    (λ { quietProtected → refl
       ; quietExposed → refl
       ; loudProtected → refl
       ; loudExposed → refl })

------------------------------------------------------------------------
-- Physical and causal promotion remains outside this finite construction:
-- there is no calibrated observation, independent conditional estimate,
-- intervention, or general biological response model in this file.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL / MEDIA PROVENANCE: EXACT OWNER RE-EXPORT
--
-- This is a cross-domain use of pre-existing Ibrahim trust/propaganda
-- finite proofs. Sound/music circulation, promotional framing, truth and
-- deceptive intent are distinct queries. These aliases contain NO new
-- mathematics and claim NO identity with Ibrahim Monster 3B objects.
--
-- Source owner:
-- DASHI.Wikimedia.IbrahimSnowballSkepticismExpertiseTrustPropagandaBidiExact
------------------------------------------------------------------------

sonicPropagandaIntentCannotDetermineTruth :
  NF.FactorsThrough
    IbrahimTrust.propagandaSurface
    IbrahimTrust.informationTruthStatus → ⊥
sonicPropagandaIntentCannotDetermineTruth =
  IbrahimTrust.propagandaIntentCannotFactorTruthStatus

sonicSameContentCannotDetermineDeceptiveIntent :
  NF.FactorsThrough
    IbrahimTrust.falseContentSurface
    IbrahimTrust.intentionReading → ⊥
sonicSameContentCannotDetermineDeceptiveIntent =
  IbrahimTrust.falseContentCannotFactorDeceptiveIntent

------------------------------------------------------------------------
-- Unsound: distinct statuses. The source does not supply an empirical
-- identification between these states, and this finite typing proves none.
------------------------------------------------------------------------

data UnsoundMeaning : Set where
  belowSelectedAudibility : UnsoundMeaning
  aboveSelectedAudibility : UnsoundMeaning
  maskedWithinAudibleBand : UnsoundMeaning
  unrealisedFuturePossibility : UnsoundMeaning

inaudibleIsNotUnrealised :
  belowSelectedAudibility ≡ unrealisedFuturePossibility → ⊥
inaudibleIsNotUnrealised ()

maskedIsNotUnrealised :
  maskedWithinAudibleBand ≡ unrealisedFuturePossibility → ⊥
maskedIsNotUnrealised ()

data AcousticEvidenceCreatesCausalAuthority : Set where
data MetaphorCreatesBiologicalInfectionProof : Set where
data MirrorWordCreatesPhysicalIdentity : Set where
data FictionalDateCreatesVerifiedEvent : Set where

noCausalityFromLabel : AcousticEvidenceCreatesCausalAuthority → ⊥
noCausalityFromLabel ()

noPathogenFromMetaphor : MetaphorCreatesBiologicalInfectionProof → ⊥
noPathogenFromMetaphor ()

noSameObjectFromMirrorWord : MirrorWordCreatesPhysicalIdentity → ⊥
noSameObjectFromMirrorWord ()

noEventFromFictionalDate : FictionalDateCreatesVerifiedEvent → ⊥
noEventFromFictionalDate ()

------------------------------------------------------------------------
-- All imported modules own their original theorems. This file only owns
-- its explicit finite witness and semantic distinctions. External
-- calibration, causality, legal conclusions and TOE/Monster identification
-- are never promoted here.
------------------------------------------------------------------------
