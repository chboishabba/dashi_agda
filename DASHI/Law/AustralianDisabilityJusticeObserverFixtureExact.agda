module DASHI.Law.AustralianDisabilityJusticeObserverFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ObserverSituatedReasonablenessExact as Situated
import DASHI.Law.SensibLawExpertEvidenceSituatedObserverExact as ExpertSituated

------------------------------------------------------------------------
-- AUSTRALIAN DISABILITY-JUSTICE OBSERVER FIXTURE
--
-- Source-bounded child over the generic situated-observer and expert-evidence
-- adapters.  The AHRC source is about disability and the Australian criminal
-- justice system.  It does not, by itself, pay autism-specific, family-court,
-- clinical, diagnostic, truth, credibility, or case-specific conclusions.
------------------------------------------------------------------------

ahrcEqualBeforeLawSource : Source.AttributedSource
ahrcEqualBeforeLawSource = Source.mkNoDOISource
  "Australian Human Rights Commission"
  "Equal Before the Law: Towards Disability Justice Strategies"
  "Australian Human Rights Commission"
  "2014"
  "https://humanrights.gov.au/resource-hub/by-resource-type/publications/disability-rights/policy-reports-disability/equal-law"
  Source.institutionalSource
  "Institutional source for bounded propositions about disability-related communication barriers, negative assumptions, credibility assessments, participation barriers, and the need for communication supports/adjustments in the Australian criminal justice system. It does not automatically generalise to autism-specific propositions, family-court proceedings, or any individual case."
  Source.publicAttribution

australianDisabilityJusticeSources : List Source.AttributedSource
australianDisabilityJusticeSources = ahrcEqualBeforeLawSource ∷ []

australianDisabilityJusticeSourceAtlas : Source.AttributedSourceAtlas
australianDisabilityJusticeSourceAtlas = Source.mkSourceAtlas
  "Australian disability justice observer source atlas"
  "DASHI.Law.AustralianDisabilityJusticeObserverFixtureExact"
  australianDisabilityJusticeSources
  "Bounded institutional evidence on disability, communication, credibility and participation barriers in Australian criminal justice; no autism-specific, family-court or case-specific promotion."

parentSituatedReasonablenessBoundary : Situated.SituatedReasonablenessBoundary
parentSituatedReasonablenessBoundary = Situated.canonicalSituatedReasonablenessBoundary

parentExpertSituatedBoundary : ExpertSituated.ExpertSituatedObserverBoundary
parentExpertSituatedBoundary = ExpertSituated.canonicalExpertSituatedObserverBoundary

record AustralianDisabilityJusticeObserverBoundary : Set where
  constructor australianDisabilityJusticeObserverBoundary
  field
    ahrcSourceBound : Bool
    negativeAssumptionsCanAffectCredibilityAssessment : Bool
    communicationSupportAndAdjustmentCoordinateLocated : Bool
    disabilitySourceAutomaticallyPaysAutismSpecificClaim : Bool
    criminalJusticeSourceAutomaticallyPaysFamilyCourtClaim : Bool
    communicationDifferenceAutomaticallyUnreliable : Bool
    adjustmentAutomaticallyEstablishesTruth : Bool
    disabilityAutomaticallyDeterminesCredibility : Bool
    sourceCitationAutomaticallyCreatesLegalAuthority : Bool
    situatedObserverParentReused : Bool
    expertSituatedObserverParentReused : Bool

open AustralianDisabilityJusticeObserverBoundary public

canonicalAustralianDisabilityJusticeObserverBoundary :
  AustralianDisabilityJusticeObserverBoundary
canonicalAustralianDisabilityJusticeObserverBoundary =
  australianDisabilityJusticeObserverBoundary
    true
    true
    true
    false
    false
    false
    false
    false
    false
    true
    true

------------------------------------------------------------------------
-- Empty bad-promotions for downstream consumers.
------------------------------------------------------------------------

data CommunicationDifferenceEstablishesUnreliability : Set where
data DisabilitySourcePaysAutismSpecificClaim : Set where
data CriminalJusticeSourcePaysFamilyCourtClaim : Set where

communicationDifferenceDoesNotEstablishUnreliability :
  CommunicationDifferenceEstablishesUnreliability → ⊥
communicationDifferenceDoesNotEstablishUnreliability ()

disabilitySourceDoesNotPayAutismSpecificClaim :
  DisabilitySourcePaysAutismSpecificClaim → ⊥
disabilitySourceDoesNotPayAutismSpecificClaim ()

criminalJusticeSourceDoesNotPayFamilyCourtClaim :
  CriminalJusticeSourcePaysFamilyCourtClaim → ⊥
criminalJusticeSourceDoesNotPayFamilyCourtClaim ()
