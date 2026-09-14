module DASHI.Law.SensibLawExpertEvidenceSituatedObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Law.AustralianFamilyReportWriterIntegrityExact as Family
import DASHI.Core.ObserverSituatedReasonablenessExact as Situated
import DASHI.Core.FragmentationCompositionExact as Fragmentation
import DASHI.Law.SensibLawEpistemicConsequenceBoundaryExact as Consequence

------------------------------------------------------------------------
-- EXPERT EVIDENCE × SITUATED OBSERVER ADAPTER
--
-- Thin child over the existing expert-production, family-report, situated-
-- observer, fragmentation and epistemic-consequence parents.  It does not
-- create a new credibility theory, trauma diagnosis, neurodivergence model,
-- truth criterion or legal rule.
------------------------------------------------------------------------

parentExpertProductionBoundary : Expert.ExpertProductionBoundary
parentExpertProductionBoundary = Expert.canonicalExpertProductionBoundary

parentFamilyReportIntegrityBoundary : Family.AustralianFamilyReportWriterBoundary
parentFamilyReportIntegrityBoundary = Family.canonicalAustralianFamilyReportWriterBoundary

parentSituatedReasonablenessBoundary : Situated.SituatedReasonablenessBoundary
parentSituatedReasonablenessBoundary = Situated.canonicalSituatedReasonablenessBoundary

parentFragmentationBoundary : Fragmentation.FragmentationBoundary
parentFragmentationBoundary = Fragmentation.canonicalFragmentationBoundary

parentEpistemicConsequenceBoundary : Consequence.EpistemicConsequenceBoundary
parentEpistemicConsequenceBoundary = Consequence.canonicalEpistemicConsequenceBoundary

------------------------------------------------------------------------
-- Consumer-facing observation state.
--
-- The purpose is to keep the report-production surface, presentation surface,
-- observer assumptions and downstream consequence coordinates separately
-- inspectable.  No field is a truth primitive.
------------------------------------------------------------------------

record ExpertSituatedObservationState : Set where
  constructor expertSituatedObservationState
  field
    acquiredEvidenceReference : String
    excludedEvidenceReference : String
    observationConditionReference : String
    affectivePresentationReference : String
    narrativePresentationReference : String
    observerExpectationReference : String
    situatedContextReference : String
    uncertainty : Consequence.EpistemicUncertainty
    consequenceSeverity : Consequence.ConsequenceSeverity
    reversibility : Consequence.Reversibility

open ExpertSituatedObservationState public

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record ExpertSituatedObserverBoundary : Set where
  constructor expertSituatedObserverBoundary
  field
    parentExpertProductionReused : Bool
    parentFamilyReportIntegrityReused : Bool
    parentSituatedReasonablenessReused : Bool
    parentFragmentationReused : Bool
    parentEpistemicConsequenceReused : Bool
    affectivePresentationAutomaticallyTruth : Bool
    narrativeCoherenceAutomaticallyTruth : Bool
    socialNormConformityAutomaticallyCredibility : Bool
    observerMismatchAutomaticallyObservedPersonDefect : Bool
    fragmentedPresentationAutomaticallyTrauma : Bool
    atypicalPresentationAutomaticallyNeurodivergence : Bool
    highUncertaintyAutomaticallyUnderlyingAccountFalse : Bool
    severeConsequenceAutomaticallyIllegality : Bool
    observerAdjustmentAutomaticallyTruth : Bool
    joinedObserverRetainsSituatedContext : Bool

open ExpertSituatedObserverBoundary public

canonicalExpertSituatedObserverBoundary : ExpertSituatedObserverBoundary
canonicalExpertSituatedObserverBoundary =
  expertSituatedObserverBoundary
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
    false
    true

------------------------------------------------------------------------
-- Explicit empty bad-promotion propositions for downstream reuse.
------------------------------------------------------------------------

data AffectivePresentationEstablishesTruth : Set where
data NarrativeCoherenceEstablishesTruth : Set where
data SocialConformityEstablishesCredibility : Set where
data ObserverMismatchEstablishesObservedPersonDefect : Set where
data FragmentationEstablishesTrauma : Set where
data AtypicalPresentationEstablishesNeurodivergence : Set where

affectivePresentationDoesNotEstablishTruth :
  AffectivePresentationEstablishesTruth → ⊥
affectivePresentationDoesNotEstablishTruth ()

narrativeCoherenceDoesNotEstablishTruth :
  NarrativeCoherenceEstablishesTruth → ⊥
narrativeCoherenceDoesNotEstablishTruth ()

socialConformityDoesNotEstablishCredibility :
  SocialConformityEstablishesCredibility → ⊥
socialConformityDoesNotEstablishCredibility ()

observerMismatchDoesNotEstablishObservedPersonDefect :
  ObserverMismatchEstablishesObservedPersonDefect → ⊥
observerMismatchDoesNotEstablishObservedPersonDefect ()

fragmentationDoesNotEstablishTrauma : FragmentationEstablishesTrauma → ⊥
fragmentationDoesNotEstablishTrauma ()

atypicalPresentationDoesNotEstablishNeurodivergence :
  AtypicalPresentationEstablishesNeurodivergence → ⊥
atypicalPresentationDoesNotEstablishNeurodivergence ()
