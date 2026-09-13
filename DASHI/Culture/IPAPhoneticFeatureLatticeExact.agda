module DASHI.Culture.IPAPhoneticFeatureLatticeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Culture.LinguisticAnthropologyCommunicativeEventPaymentReceiptExact as Event

------------------------------------------------------------------------
-- IPA PHONETIC FEATURE LATTICE
--
-- Source owner:
-- International Phonetic Association, official IPA Chart.
-- Current official chart family inspected 2026-09-10; the Association states
-- that the IPA is a notational standard for phonetic representation across
-- languages. The chart keeps pulmonic/non-pulmonic consonants, vowels,
-- diacritics, suprasegmentals, tones/word accents and other symbols distinct.
--
-- This is a PHONETIC feature owner. It does not claim that an IPA symbol is a
-- phoneme of any language. Phone -> phoneme requires language-relative
-- contrast/distribution evidence on a concrete language/event corpus.
------------------------------------------------------------------------

data PlaceOfArticulation : Set where
  bilabial labiodental dental alveolar postalveolar retroflex palatal velar uvular pharyngeal glottal : PlaceOfArticulation

data MannerOfArticulation : Set where
  plosive nasal trill tapFlap fricative lateralFricative approximant lateralApproximant : MannerOfArticulation

data Voicing : Set where
  voiceless voiced : Voicing

record PulmonicConsonantCell : Set where
  constructor pulmonic-consonant-cell
  field
    symbol : String
    place : PlaceOfArticulation
    manner : MannerOfArticulation
    voicing : Voicing
    officialChartReference : String
open PulmonicConsonantCell public

data VowelHeight : Set where
  close nearClose closeMid mid openMid nearOpen open : VowelHeight

data VowelBackness : Set where
  front central back : VowelBackness

data Rounding : Set where
  unrounded rounded : Rounding

record VowelCell : Set where
  constructor vowel-cell
  field
    symbol : String
    height : VowelHeight
    backness : VowelBackness
    rounding : Rounding
    officialChartReference : String
open VowelCell public

data SecondaryPhoneticLayer : Set where
  nonPulmonicConsonant diacritic suprasegmental toneWordAccent otherSymbol : SecondaryPhoneticLayer

record IPAChartArchitecture : Set where
  constructor ipa-chart-architecture
  field
    pulmonicConsonantsUsePlaceMannerVoicing : Bool
    vowelsUseHeightBacknessRounding : Bool
    nonPulmonicsSeparate : Bool
    diacriticsSeparate : Bool
    suprasegmentalsSeparate : Bool
    tonesSeparate : Bool
    chartIsCompleteInventoryOfLanguagePhonemes : Bool
open IPAChartArchitecture public

canonicalIPAChartArchitecture : IPAChartArchitecture
canonicalIPAChartArchitecture =
  ipa-chart-architecture true true true true true true false

------------------------------------------------------------------------
-- Event-bound phonetic transcription receipt.
------------------------------------------------------------------------

record EventPhoneticTranscriptionReceipt : Set where
  constructor event-phonetic-transcription-receipt
  field
    event : Event.CommunicativeEventIdentity
    speechCarrier : Event.SpeechCarrierReceipt
    speechCarrierUsesSameEvent : Event.event speechCarrier ≡ event
    transcriptionReference : String
    transcriptionRevision : String
    ipaChartReference : String
    segmentInventoryReference : String
    transcriptionGranularity : String
    transcriberReference : String
    uncertaintyReference : String
    acousticOrAuditorySupportReference : String
    narrowOrBroadDeclared : Bool
    sourceBound : Bool
open EventPhoneticTranscriptionReceipt public

------------------------------------------------------------------------
-- Phone/phoneme firewall.
------------------------------------------------------------------------

record LanguagePhonemeContrastReceipt : Set where
  constructor language-phoneme-contrast-receipt
  field
    languageOrVariety : String
    phoneA : String
    phoneB : String
    contrastEvidenceReference : String
    minimalPairOrDistributionReference : String
    meaningContrastEstablished : Bool
    samePhonemeEstablished : Bool
open LanguagePhonemeContrastReceipt public

data IPAFeatureCellCreatesPhoneme : Set where
data SamePhoneAcrossLanguagesCreatesSamePhoneme : Set where
data OrthographicLetterCreatesPhone : Set where
data PhoneticTranscriptionCreatesSocialMeaning : Set where

ipaCellDoesNotCreatePhoneme : IPAFeatureCellCreatesPhoneme → ⊥
ipaCellDoesNotCreatePhoneme ()

samePhoneDoesNotCreateSameCrossLanguagePhoneme : SamePhoneAcrossLanguagesCreatesSamePhoneme → ⊥
samePhoneDoesNotCreateSameCrossLanguagePhoneme ()

letterDoesNotCreatePhone : OrthographicLetterCreatesPhone → ⊥
letterDoesNotCreatePhone ()

phoneticTranscriptionDoesNotCreateSocialMeaning : PhoneticTranscriptionCreatesSocialMeaning → ⊥
phoneticTranscriptionDoesNotCreateSocialMeaning ()

record IPAPhoneticFeatureBoundary : Set where
  constructor ipa-phonetic-feature-boundary
  field
    officialChartSourceBound : Bool
    featureAxesExplicit : Bool
    eventTranscriptionSameObjectBound : Bool
    phoneAndPhonemeSeparated : Bool
    phoneticsAndSocialMeaningSeparated : Bool
    ipaSymbolAutomaticallyLanguagePhoneme : Bool
open IPAPhoneticFeatureBoundary public

canonicalIPAPhoneticFeatureBoundary : IPAPhoneticFeatureBoundary
canonicalIPAPhoneticFeatureBoundary =
  ipa-phonetic-feature-boundary true true true true true false
