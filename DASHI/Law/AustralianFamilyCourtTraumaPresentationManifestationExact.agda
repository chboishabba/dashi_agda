module DASHI.Law.AustralianFamilyCourtTraumaPresentationManifestationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawExpertEvidenceSituatedObserverExact as ExpertSituated
import DASHI.Law.AustralianDisabilityJusticeObserverFixtureExact as Disability
import DASHI.Law.TraumaNarrativeEvidenceBoundaryExact as TraumaEvidence
import DASHI.Law.SensibLawEpistemicConsequenceBoundaryExact as Consequence

------------------------------------------------------------------------
-- FAMILY-COURT TRAUMA / PRESENTATION MANIFESTATION
--
-- News-source fixture over the generic expert/situated-observer and
-- uncertainty/consequence parents.  It retains only source-class propositions
-- and does not convert reporting into a judgment, transcript, expert report,
-- clinical record, case finding, professional breach, or systemic theorem.
------------------------------------------------------------------------

abcFamilyCourt2026Source : Source.AttributedSource
abcFamilyCourt2026Source = Source.mkNoDOISource
  "Heidi Davoren and Adelaide Miller"
  "Alleged DV victim labelled 'difficult witness', family court permanently removes children"
  "ABC News — Specialist Reporting Team"
  "2026"
  "https://www.abc.net.au/news/2026-07-17/alleged-dv-victim-loses-custody-of-children-in-family-court/106826526"
  Source.newsSource
  "News manifestation used only for bounded reporting coordinates: a reported witness-characterisation, quoted commentary separating narrative smoothness from truth, and reported coexistence of acknowledged uncertainty with a highly consequential parenting order. Primary court and expert records remain separate dependencies."
  Source.publicAttribution

familyCourtTraumaPresentationSources : List Source.AttributedSource
familyCourtTraumaPresentationSources = abcFamilyCourt2026Source ∷ []

familyCourtTraumaPresentationAtlas : Source.AttributedSourceAtlas
familyCourtTraumaPresentationAtlas = Source.mkSourceAtlas
  "Australian family-court trauma/presentation manifestation source atlas"
  "DASHI.Law.AustralianFamilyCourtTraumaPresentationManifestationExact"
  familyCourtTraumaPresentationSources
  "Single news manifestation retained as reporting; no case-specific truth, diagnosis, legal error, breach or systemic generalisation is imported."

parentExpertSituatedBoundary : ExpertSituated.ExpertSituatedObserverBoundary
parentExpertSituatedBoundary = ExpertSituated.canonicalExpertSituatedObserverBoundary

parentDisabilityJusticeBoundary : Disability.AustralianDisabilityJusticeObserverBoundary
parentDisabilityJusticeBoundary = Disability.canonicalAustralianDisabilityJusticeObserverBoundary

parentTraumaNarrativeEvidenceBoundary : TraumaEvidence.TraumaNarrativeEvidenceBoundary
parentTraumaNarrativeEvidenceBoundary = TraumaEvidence.canonicalTraumaNarrativeEvidenceBoundary

-- Repository-local analytical classification of the reported combination of
-- unresolved uncertainty and a highly consequential, difficult-to-reverse
-- order.  This is not a quotation, judicial characterisation, legal threshold,
-- or source holding.
manifestationAnalyticalConsequenceState : Consequence.EpistemicConsequenceState
manifestationAnalyticalConsequenceState = Consequence.epistemicConsequenceState
  Consequence.unresolvedUncertainty
  Consequence.extremeConsequence
  Consequence.difficultToReverse

-- Backward-compatible name retained as a non-authoritative alias.
reportedConsequenceState : Consequence.EpistemicConsequenceState
reportedConsequenceState = manifestationAnalyticalConsequenceState

record FamilyCourtTraumaPresentationBoundary : Set where
  constructor familyCourtTraumaPresentationBoundary
  field
    abc2026SourceBound : Bool
    expertSituatedObserverParentReused : Bool
    disabilityJusticeParentReused : Bool
    traumaNarrativeEvidenceParentReused : Bool
    difficultWitnessCharacterisationReported : Bool
    fragmentedNarrationTruthBoundaryReported : Bool
    considerableUncertaintyAndSevereOrderReported : Bool
    newsArticleAutomaticallyPrimaryCourtRecord : Bool
    newsArticleAutomaticallyExpertReport : Bool
    reportedNeurodivergenceAutomaticallyExplainsWitnessPresentation : Bool
    reportedTraumaAutomaticallyEstablishesUnderlyingAllegationTruth : Bool
    difficultWitnessCharacterisationAutomaticallyEstablishesUnreliability : Bool
    severeOrderAutomaticallyEstablishesLegalError : Bool
    articleAutomaticallyEstablishesSystemicGeneralisation : Bool
    analyticalConsequenceMappingAutomaticallySourceHolding : Bool

open FamilyCourtTraumaPresentationBoundary public

canonicalFamilyCourtTraumaPresentationBoundary :
  FamilyCourtTraumaPresentationBoundary
canonicalFamilyCourtTraumaPresentationBoundary =
  familyCourtTraumaPresentationBoundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
