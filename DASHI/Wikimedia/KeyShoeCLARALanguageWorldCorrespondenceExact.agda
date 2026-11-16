module DASHI.Wikimedia.KeyShoeCLARALanguageWorldCorrespondenceExact where

------------------------------------------------------------------------
-- KEYSHOE / CLARA R13 <-> SLR PARSER -> PNF -> WORLD-ALGEBRA
--
-- Source: @bigshoesjqz English Radial R13 / CLARA J13 screenshots
-- supplied 2026-11-16. This code consumes, but does not redefine, the
-- provisional 13-body/26-letter chart and its source-scoped dihedral action.
-- The Hebrew WLC Exodus 72-indexed Shem extraction is an independent source.
-- There is no creator-supplied Hebrew->R13 transliteration or meaning map:
-- no Hebrew reading, modular j identity, physical detector or law is inferred.
--
-- The strict numeric/spaCy PNF is distinct from the evidential PNF and
-- from DASHI's world PNF. The explicit review/interpretation square below
-- names the missing warrant; mere text identity never fills it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.KeyShoeCLARAR13DihedralExact as R13
import DASHI.Wikimedia.KeyShoeCLARAOperatorBoundaryExact as CLARA
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.SensibLawSpacyPredicateNormalFormBridgeExact as Spacy
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as Logical
import DASHI.WorldModel.PredicateNormalWorldModelCore as World

------------------------------------------------------------------------
-- 1. Genuine chart facts: the full R13 letter slot is body + side.
-- The body-only projection forgets a meaningful alphabet distinction.
------------------------------------------------------------------------

bodyOfLetter : R13.LetterSlot → R13.Body13
bodyOfLetter (R13.slot body side) = body

sideOfLetter : R13.LetterSlot → R13.Side
sideOfLetter (R13.slot body side) = side

fullLetterRoundTrip :
  (letter : R13.LetterSlot) →
  R13.slot (bodyOfLetter letter) (sideOfLetter letter) ≡ letter
fullLetterRoundTrip (R13.slot body side) = refl

bodyForgetsPairSwap :
  (letter : R13.LetterSlot) →
  bodyOfLetter (R13.pairSwap letter) ≡ bodyOfLetter letter
bodyForgetsPairSwap (R13.slot body side) = refl

bodyRespectsAlphabetReversal :
  (letter : R13.LetterSlot) →
  bodyOfLetter (R13.alphabetReversal letter)
  ≡ R13.reflectBody (bodyOfLetter letter)
bodyRespectsAlphabetReversal (R13.slot body side) = refl

differentLetterSides : R13.first ≡ R13.second → ⊥
differentLetterSides ()

-- Concrete obstruction to treating the 13-body quotient as a *lossless*
-- language encoding. In particular, MN/M and MN/N share a body address.
bodyOnlyCannotAnswerLetterSide :
  Descent.ConsumerSufficient bodyOfLetter sideOfLetter → ⊥
bodyOnlyCannotAnswerLetterSide sufficient =
  differentLetterSides
    (sufficient
      (R13.slot R13.b3 R13.first)
      (R13.slot R13.b3 R13.second)
      refl)

------------------------------------------------------------------------
-- 2. The only legal meaning-preserving correspondence is consumer-indexed.
-- A non-Latin corpus (including Hebrew) needs an independently supplied
-- encoding/transliteration and an actual fibre-constancy warrant.
------------------------------------------------------------------------

record SourceEncodingForConsumer
    (RawSymbol Outcome : Set) : Set₁ where
  constructor sourceEncodingForConsumer
  field
    encode : RawSymbol → R13.LetterSlot
    consumer : RawSymbol → Outcome
    bodyAdequateForConsumer :
      Descent.ConsumerSufficient
        (λ symbol → bodyOfLetter (encode symbol))
        consumer

sourceBodyAgreementPreservesConsumer :
  ∀ {RawSymbol Outcome : Set} →
  (bridge : SourceEncodingForConsumer RawSymbol Outcome) →
  (left right : RawSymbol) →
  bodyOfLetter (SourceEncodingForConsumer.encode bridge left)
  ≡ bodyOfLetter (SourceEncodingForConsumer.encode bridge right) →
  SourceEncodingForConsumer.consumer bridge left
  ≡ SourceEncodingForConsumer.consumer bridge right
sourceBodyAgreementPreservesConsumer bridge left right same =
  SourceEncodingForConsumer.bodyAdequateForConsumer bridge
    left right same

------------------------------------------------------------------------
-- 3. Existing SLR numeric PNF -> reviewed logical PNF -> world algebra.
-- This is a transport *contract*, not evidence that an external parser
-- or interpreter has supplied a reviewed, adequate implementation.
------------------------------------------------------------------------

record ParserPNFWorldAlgebraCorrespondence
    {source : Cone.NaturalLanguageExperimentalAssertion}
    (numeric : Spacy.SensibLawNumericPNFReceipt source)
    (logical : Cone.PNFCompilationReceipt source)
    (world : World.PredicateNormalWorldModelCore) : Set₁ where
  constructor parserPNFWorldAlgebraCorrespondence
  field
    numericLogicalCorrespondence :
      Spacy.ParserToEvidencePNFCorrespondence numeric logical

    observedSource : World.Observation world

    licensedInterpretation :
      Logical.PredicateNormalAssertion → World.PNF world

    interpretationAgreesWithWorldNormalisation :
      licensedInterpretation (Cone.compiled logical)
      ≡ World.normalize world (World.encodeCarrier world observedSource)

open ParserPNFWorldAlgebraCorrespondence public

sourceTextSurvivesNumericToLogical :
  ∀ {source : Cone.NaturalLanguageExperimentalAssertion}
    {numeric : Spacy.SensibLawNumericPNFReceipt source}
    {logical : Cone.PNFCompilationReceipt source}
    {world : World.PredicateNormalWorldModelCore} →
  ParserPNFWorldAlgebraCorrespondence numeric logical world →
  Spacy.canonicalText numeric
  ≡ Logical.naturalLanguage (Cone.compiled logical)
sourceTextSurvivesNumericToLogical bridge =
  Spacy.parserTextReachesLogicalText
    (numericLogicalCorrespondence bridge)

reviewedInterpretationCommutesWithWorld :
  ∀ {source : Cone.NaturalLanguageExperimentalAssertion}
    {numeric : Spacy.SensibLawNumericPNFReceipt source}
    {logical : Cone.PNFCompilationReceipt source}
    {world : World.PredicateNormalWorldModelCore} →
  (bridge : ParserPNFWorldAlgebraCorrespondence
    {source} numeric logical world) →
  licensedInterpretation bridge (Cone.compiled logical)
  ≡ World.normalize world
      (World.encodeCarrier world (observedSource bridge))
reviewedInterpretationCommutesWithWorld bridge =
  interpretationAgreesWithWorldNormalisation bridge

------------------------------------------------------------------------
-- 4. CLARA's 14 D-stages are typed observer landmarks, not R13 letters
-- or automatic legal inference stages. No exported map confuses them.
------------------------------------------------------------------------

record StageIndexedWorldObservation
    (world : World.PredicateNormalWorldModelCore) : Set₁ where
  constructor stageIndexedWorldObservation
  field
    observeAtStage :
      CLARA.ObserverDStage → World.Observation world

    -- Source-stage naming says nothing by itself about the interpretation
    -- or about an independently calibrated detector measurement.
    sourceStageEvidenceReference : String

------------------------------------------------------------------------
-- The type-level result is deliberately limited:
-- * R13 full slot <-> (body,side) has exact round trip.
-- * R13 body-only projection is not sufficient for side-sensitive reading.
-- * Source-specific semantic and world-model coherence must be supplied.
-- * No Hebrew/English equivalence or theorem receipt is fabricated.
------------------------------------------------------------------------
