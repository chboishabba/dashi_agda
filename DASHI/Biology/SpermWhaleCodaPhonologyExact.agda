module DASHI.Biology.SpermWhaleCodaPhonologyExact where

-- Source-attributed, evidence-bounded phonological comparison, 25 October 2026.
-- A sperm whale is NOT asserted to speak Mandarin.  Acoustic structure, its
-- possible communicative function, and lexical meaning are different queries.
--
-- Original sources (in date order):
-- Sharma et al. (2024), Nature Communications, 10.1038/s41467-024-47221-8.
-- Beguš et al. (2025), Open Mind, 10.1162/opmi.a.252.
-- Beguš et al. (2026), Proceedings B, 10.1098/rspb.2025.2994.
-- The finite witnesses below are OUR synthetic countermodels, NOT data
-- transcribed from any of the papers.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.AnimalCommunicationLatentExact as Latent
import DASHI.Biology.AnimalCommunicationSemanticEvidenceExact as Semantic
import DASHI.Culture.PhonologicalFeatureMatrixContrastExact as Phonology

------------------------------------------------------------------------
-- Independent SOURCE (click count/timing) and FILTER (spectral formants)
-- coordinates.  Terms here are analogical acoustic descriptors, NOT
-- identified whale phonemes or translations of human vowels.
------------------------------------------------------------------------

data CodaRhythm : Set where
  regularRhythm : CodaRhythm
  otherRhythm : CodaRhythm
  rhythmUnresolved : CodaRhythm

data CodaTempo : Set where
  relativelySlow : CodaTempo
  relativelyFast : CodaTempo
  tempoUnresolved : CodaTempo

data ExchangeRubato : Set where
  rubatoCandidate : ExchangeRubato
  noRubatoDetected : ExchangeRubato
  rubatoUnresolved : ExchangeRubato

data EdgeOrnament : Set where
  ornamentCandidate : EdgeOrnament
  noOrnamentDetected : EdgeOrnament
  ornamentUnresolved : EdgeOrnament

data FilterQuality : Set where
  aLike : FilterQuality
  iLike : FilterQuality
  qualityUnresolved : FilterQuality

data FormantTrajectory : Set where
  flatTrajectory : FormantTrajectory
  risingTrajectory : FormantTrajectory
  fallingTrajectory : FormantTrajectory
  risingFallingTrajectory : FormantTrajectory
  fallingRisingTrajectory : FormantTrajectory
  trajectoryUnresolved : FormantTrajectory

data CodaDurationClass : Set where
  shortCandidate : CodaDurationClass
  longCandidate : CodaDurationClass
  durationUnresolved : CodaDurationClass

record SourceCoordinates : Set where
  constructor sourceCoordinates
  field
    clickCount : Nat
    rhythm : CodaRhythm
    tempo : CodaTempo
    rubato : ExchangeRubato
    ornament : EdgeOrnament
open SourceCoordinates public

record FilterCoordinates : Set where
  constructor filterCoordinates
  field
    vowelQuality : FilterQuality
    formantTrajectory : FormantTrajectory
open FilterCoordinates public

record CodaAcousticCandidate : Set where
  constructor codaAcousticCandidate
  field
    eventReference : String
    recordingProvenance : String
    producerIdentityReference : String
    source : SourceCoordinates
    filter : FilterCoordinates
    durationClass : CodaDurationClass
open CodaAcousticCandidate public

-- This is *product-type independence*: either quality can be represented
-- with the same timing.  It does NOT claim equal empirical frequencies or
-- assert the unconditional statistical independence of random variables.

syntheticFourClickSource : SourceCoordinates
syntheticFourClickSource =
  sourceCoordinates (suc (suc (suc (suc zero))))
    regularRhythm relativelySlow rubatoUnresolved ornamentUnresolved

syntheticA : CodaAcousticCandidate
syntheticA = codaAcousticCandidate
  "synthetic only: A" "no field recording" "unknown emitter"
  syntheticFourClickSource
  (filterCoordinates aLike flatTrajectory)
  durationUnresolved

syntheticI : CodaAcousticCandidate
syntheticI = codaAcousticCandidate
  "synthetic only: I" "no field recording" "unknown emitter"
  syntheticFourClickSource
  (filterCoordinates iLike flatTrajectory)
  durationUnresolved

sameSourceDifferentFilter :
  source syntheticA ≡ source syntheticI
sameSourceDifferentFilter = refl

aAndIAreDifferentConstructors : aLike ≡ iLike → ⊥
aAndIAreDifferentConstructors ()

------------------------------------------------------------------------
-- Mandarin is a HUMAN-LANGUAGE comparison target.  The four tone labels
-- are lexical contrast *within Mandarin*.  No whale semantic mapping is
-- introduced by sharing a source/filter coordinate description.
------------------------------------------------------------------------

data MandarinTone : Set where
  levelTone : MandarinTone
  risingTone : MandarinTone
  fallingRisingTone : MandarinTone
  fallingTone : MandarinTone

data MandarinVowel : Set where
  aVowel : MandarinVowel
  iVowel : MandarinVowel
  otherVowel : MandarinVowel

record HumanMandarinPhonologicalForm : Set where
  constructor humanMandarinPhonologicalForm
  field
    tone : MandarinTone
    humanVowel : MandarinVowel

record CrossSpeciesPhoneticAnalogy : Set where
  constructor crossSpeciesPhoneticAnalogy
  field
    humanForm : HumanMandarinPhonologicalForm
    whaleForm : CodaAcousticCandidate
    comparisonSource : String
    structuralComparisonOnly : Bool
    comparisonOnlyProof : structuralComparisonOnly ≡ true
    semanticEquivalenceClaimed : Bool
    noSemanticEquivalenceProof : semanticEquivalenceClaimed ≡ false

syntheticMandarinComparison : CrossSpeciesPhoneticAnalogy
syntheticMandarinComparison =
  crossSpeciesPhoneticAnalogy
    (humanMandarinPhonologicalForm fallingRisingTone aVowel)
    syntheticA
    "Beguš et al. 2025/2026: Mandarin is an acoustic/phonological analogy"
    true refl false refl

------------------------------------------------------------------------
-- Original authorship / chronology / epistemic status.
-- A source ledger is not a replication, a meaning dictionary, or proof.
------------------------------------------------------------------------

sharma2024 : Source.AttributedSource
sharma2024 =
  Source.mkDOISource
    "Pratyusha Sharma; Shane Gero; Roger Payne; David F. Gruber; Daniela Rus; Antonio Torralba; Jacob Andreas"
    "Contextual and combinatorial structure in sperm whale vocalisations"
    "Nature Communications 15:3617" "2024"
    "10.1038/s41467-024-47221-8"
    "https://doi.org/10.1038/s41467-024-47221-8"
    Source.academicArticleSource
    "rhythm, tempo, rubato and ornamentation; source reports context and combination, not translations"
    Source.publicAttribution

begus2025 : Source.AttributedSource
begus2025 =
  Source.mkDOISource
    "Gašper Beguš; Ronald L. Sprouse; Andrej Leban; Miles Silva; Shane Gero"
    "Vowel- and Diphthong-Like Spectral Patterns in Sperm Whale Codas"
    "Open Mind 9:1849-1874" "2025"
    "10.1162/opmi.a.252"
    "https://doi.org/10.1162/opmi.a.252"
    Source.academicArticleSource
    "candidate a/i formants and diphthong-like trajectories; Mandarin source/filter analogy; no decoded lexical meaning"
    Source.publicAttribution

begus2026 : Source.AttributedSource
begus2026 =
  Source.mkDOISource
    "Gašper Beguš; Maksymilian Dąbkowski; Ronald L. Sprouse; David F. Gruber; Shane Gero"
    "The phonology of sperm whale coda vowels"
    "Proceedings of the Royal Society B 293:20252994" "2026"
    "10.1098/rspb.2025.2994"
    "https://doi.org/10.1098/rspb.2025.2994"
    Source.academicArticleSource
    "five source-reported phonology results; not a proof of Mandarin speech, whale semantics or dataset replication"
    Source.publicAttribution

originalSourceAtlas : Source.AttributedSourceAtlas
originalSourceAtlas =
  Source.mkSourceAtlas
    "Sperm whale coda acoustic structure (2024-2026)"
    "DASHI.Biology.SpermWhaleCodaPhonologyExact"
    (sharma2024 ∷ begus2025 ∷ begus2026 ∷ [])
    "Original publications credited in chronology; all data-dependent results remain external-source claims"

data ReportedPattern : Set where
  timingTypeInteractsWithFilterQuality : ReportedPattern
  aLikeGenerallyLongerThanILike : ReportedPattern
  shortAndLongILikeCandidates : ReportedPattern
  individualBaselineDurationVariation : ReportedPattern
  edgeClickCoarticulationLikePatterns : ReportedPattern

record SourceReportedFinding : Set where
  constructor sourceReportedFinding
  field
    observedPatternClaim : ReportedPattern
    sourcePaper : Source.AttributedSource
    replicatedFromUnderlyingData : Bool
    independentSemanticPayment : Semantic.PaymentStatus
open SourceReportedFinding public

-- These are five *attributed claims* from the 2026 paper, not five proofs of
-- empirical facts.  In particular, "generally longer" is NOT a universal
-- theorem about all a-like vs i-like codas.

five2026ReportedPatterns : List SourceReportedFinding
five2026ReportedPatterns =
  sourceReportedFinding timingTypeInteractsWithFilterQuality begus2026
    false Semantic.unpaid ∷
  sourceReportedFinding aLikeGenerallyLongerThanILike begus2026
    false Semantic.unpaid ∷
  sourceReportedFinding shortAndLongILikeCandidates begus2026
    false Semantic.unpaid ∷
  sourceReportedFinding individualBaselineDurationVariation begus2026
    false Semantic.unpaid ∷
  sourceReportedFinding edgeClickCoarticulationLikePatterns begus2026
    false Semantic.unpaid ∷ []

------------------------------------------------------------------------
-- Exact negative result: even a PERFECT acoustic-form classifier cannot
-- answer a semantic query in unrestricted worlds, because two distinct
-- semantic states can have the same acoustic readout.
-- This is a mathematical adequacy countermodel, not an observation that
-- whales lack communicative meaning.
------------------------------------------------------------------------

data SyntheticWorld : Set where
  sameCodaContextOne : SyntheticWorld
  sameCodaContextTwo : SyntheticWorld

data SyntheticAcousticReadout : Set where
  indistinguishableAcousticForm : SyntheticAcousticReadout

data SemanticQuery : Set where
  putativeMeaning : SemanticQuery

data SemanticAnswer : Set where
  possibleMeaningOne : SemanticAnswer
  possibleMeaningTwo : SemanticAnswer

acousticProjection : SyntheticWorld → SyntheticAcousticReadout
acousticProjection world = indistinguishableAcousticForm

semanticAnswer : SemanticQuery → SyntheticWorld → SemanticAnswer
semanticAnswer putativeMeaning sameCodaContextOne = possibleMeaningOne
semanticAnswer putativeMeaning sameCodaContextTwo = possibleMeaningTwo

syntheticSemantics :
  Query.QuerySemantics SyntheticWorld SemanticQuery SemanticAnswer
syntheticSemantics = Query.querySemantics semanticAnswer

soundCannotIdentifyMeaningDefect :
  Query.QueryAdequacyDefect acousticProjection syntheticSemantics putativeMeaning
soundCannotIdentifyMeaningDefect =
  Query.queryAdequacyDefect sameCodaContextOne sameCodaContextTwo refl (λ ())

soundAloneCannotDetermineMeaning :
  Query.AdequateFor acousticProjection syntheticSemantics putativeMeaning → ⊥
soundAloneCannotDetermineMeaning =
  Query.queryAdequacyDefectBlocksFactorisation soundCannotIdentifyMeaningDefect

-- Explicit reuse of canonical species-analogy, phoneme and semantic guards.
canonicalAnalogyGuard : Latent.CrossSpeciesAnalogyBoundary
canonicalAnalogyGuard = Latent.canonicalCrossSpeciesAnalogyBoundary

canonicalSemanticGuard : Semantic.CommunicationSemanticBoundary
canonicalSemanticGuard = Semantic.canonicalCommunicationSemanticBoundary

canonicalPhonemicContrastGuard : Phonology.PhonologicalFeatureMatrixBoundary
canonicalPhonemicContrastGuard = Phonology.canonicalPhonologicalFeatureMatrixBoundary
