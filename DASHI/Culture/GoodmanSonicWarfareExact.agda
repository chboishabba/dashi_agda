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
  "34 chapters and conclusion; claims indexed separately in Docs/papers/GoodmanSonicWarfare.md"

sourceCitationDoesNotPromote :
  (validation : String) →
  Receipt.promotesClaim
    (Attr.attributedSourceAtlasReceipt goodmanSources validation) ≡ false
sourceCitationDoesNotPromote validation =
  Attr.attributedSourceAtlasReceiptNonPromoting goodmanSources validation

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
-- P0 mirror: a surface label cannot establish its underlying referent.
-- "Acoustic mirror" is an engineering example, not a Goodman physical claim
-- and not evidence of an alleged Kozyrev effect.
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
