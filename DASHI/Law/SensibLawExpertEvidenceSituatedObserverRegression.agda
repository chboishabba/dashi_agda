module DASHI.Law.SensibLawExpertEvidenceSituatedObserverRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawExpertEvidenceSituatedObserverExact as SituatedExpert

-- Parent reuse must be explicit: no parallel expert-production, observer or
-- uncertainty ontology in this child adapter.
parentExpertProductionReusedRegression :
  SituatedExpert.parentExpertProductionReused
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ true
parentExpertProductionReusedRegression = refl

parentFamilyReportIntegrityReusedRegression :
  SituatedExpert.parentFamilyReportIntegrityReused
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ true
parentFamilyReportIntegrityReusedRegression = refl

parentSituatedReasonablenessReusedRegression :
  SituatedExpert.parentSituatedReasonablenessReused
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ true
parentSituatedReasonablenessReusedRegression = refl

parentFragmentationReusedRegression :
  SituatedExpert.parentFragmentationReused
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ true
parentFragmentationReusedRegression = refl

parentEpistemicConsequenceReusedRegression :
  SituatedExpert.parentEpistemicConsequenceReused
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ true
parentEpistemicConsequenceReusedRegression = refl

-- Surface presentation may not silently become truth, credibility or risk.
affectivePresentationAutomaticallyTruthRegression :
  SituatedExpert.affectivePresentationAutomaticallyTruth
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ false
affectivePresentationAutomaticallyTruthRegression = refl

narrativeCoherenceAutomaticallyTruthRegression :
  SituatedExpert.narrativeCoherenceAutomaticallyTruth
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ false
narrativeCoherenceAutomaticallyTruthRegression = refl

socialNormConformityAutomaticallyCredibilityRegression :
  SituatedExpert.socialNormConformityAutomaticallyCredibility
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ false
socialNormConformityAutomaticallyCredibilityRegression = refl

observerMismatchAutomaticallyObservedPersonDefectRegression :
  SituatedExpert.observerMismatchAutomaticallyObservedPersonDefect
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ false
observerMismatchAutomaticallyObservedPersonDefectRegression = refl

-- Consequence analysis stays analytical and non-promoting.
highUncertaintyAutomaticallyFalseRegression :
  SituatedExpert.highUncertaintyAutomaticallyUnderlyingAccountFalse
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ false
highUncertaintyAutomaticallyFalseRegression = refl

severeConsequenceAutomaticallyIllegalityRegression :
  SituatedExpert.severeConsequenceAutomaticallyIllegality
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ false
severeConsequenceAutomaticallyIllegalityRegression = refl

-- The repair is to retain observer/situated coordinates, not to infer truth.
joinedObserverRetainsContextRegression :
  SituatedExpert.joinedObserverRetainsSituatedContext
    SituatedExpert.canonicalExpertSituatedObserverBoundary
  ≡ true
joinedObserverRetainsContextRegression = refl
