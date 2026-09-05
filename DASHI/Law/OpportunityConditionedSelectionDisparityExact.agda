module DASHI.Law.OpportunityConditionedSelectionDisparityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.WandingOpportunityEligibilityHypervoxelExact as Opportunity

------------------------------------------------------------------------
-- Population disparity decomposes into exposure opportunity and conditional
-- officer selection.  These are different estimands and different producers.
------------------------------------------------------------------------

record OpportunitySelectionCounts : Set where
  constructor opportunitySelectionCounts
  field
    targetPopulationCount targetOpportunityCount targetEligibleCount targetSelectedCount : ℕ
    comparisonPopulationCount comparisonOpportunityCount comparisonEligibleCount comparisonSelectedCount : ℕ
    missingOpportunityCount missingEligibilityCount missingSelectionCount : ℕ
    countReference : String

open OpportunitySelectionCounts public

data ConditionalEstimand : Set where
  opportunityRateByGroup eligibilityGivenOpportunity selectionGivenEligibility
  unconditionalSelectionRate : ConditionalEstimand

record ConditionalRatioRequest : Set where
  constructor conditionalRatioRequest
  field
    estimand : ConditionalEstimand
    targetNumerator targetDenominator : ℕ
    comparisonNumerator comparisonDenominator : ℕ
    targetMeaning comparisonMeaning : String
    conditioningReference : String

open ConditionalRatioRequest public

opportunityRateRequest : OpportunitySelectionCounts → ConditionalRatioRequest
opportunityRateRequest s = conditionalRatioRequest
  opportunityRateByGroup
  (targetOpportunityCount s) (targetPopulationCount s)
  (comparisonOpportunityCount s) (comparisonPopulationCount s)
  "target exposure-opportunity count / target reference population count"
  "comparison exposure-opportunity count / comparison reference population count"
  "descriptive deployment/exposure opportunity estimand"

eligibilityGivenOpportunityRequest : OpportunitySelectionCounts → ConditionalRatioRequest
eligibilityGivenOpportunityRequest s = conditionalRatioRequest
  eligibilityGivenOpportunity
  (targetEligibleCount s) (targetOpportunityCount s)
  (comparisonEligibleCount s) (comparisonOpportunityCount s)
  "target legally eligible / target opportunity-exposed"
  "comparison legally eligible / comparison opportunity-exposed"
  "legal-scope conditioning estimand"

selectionGivenEligibilityRequest : OpportunitySelectionCounts → ConditionalRatioRequest
selectionGivenEligibilityRequest s = conditionalRatioRequest
  selectionGivenEligibility
  (targetSelectedCount s) (targetEligibleCount s)
  (comparisonSelectedCount s) (comparisonEligibleCount s)
  "target selected / target legally eligible"
  "comparison selected / comparison legally eligible"
  "conditional officer-selection estimand"

unconditionalSelectionRateRequest : OpportunitySelectionCounts → ConditionalRatioRequest
unconditionalSelectionRateRequest s = conditionalRatioRequest
  unconditionalSelectionRate
  (targetSelectedCount s) (targetPopulationCount s)
  (comparisonSelectedCount s) (comparisonPopulationCount s)
  "target selected / target reference population"
  "comparison selected / comparison reference population"
  "mixes deployment opportunity, eligibility and selection; not a pure selection estimand"

------------------------------------------------------------------------
-- BIDI decomposition.
------------------------------------------------------------------------

data OpportunityDisparityClaim : Set where
  deploymentOpportunityDisparity eligibilityConditionalDisparity
  officerSelectionConditionalDisparity unconditionalObservedDisparity : OpportunityDisparityClaim

data OpportunityDisparityProducer : Set where
  populationExposureFrame opportunityCrossTab legalEligibilityCrossTab selectedEligibleCrossTab
  completeDecompositionReceipt : OpportunityDisparityProducer

reverseOpportunityDisparity : OpportunityDisparityClaim → OpportunityDisparityProducer
reverseOpportunityDisparity deploymentOpportunityDisparity = opportunityCrossTab
reverseOpportunityDisparity eligibilityConditionalDisparity = legalEligibilityCrossTab
reverseOpportunityDisparity officerSelectionConditionalDisparity = selectedEligibleCrossTab
reverseOpportunityDisparity unconditionalObservedDisparity = completeDecompositionReceipt

record OpportunityDisparityCutset : Set where
  constructor opportunityDisparityCutset
  field
    populationFrameClosed : Bool
    opportunityClosed : Bool
    eligibilityClosed : Bool
    selectionClosed : Bool
    missingnessClosed : Bool
    cutsetReference : String

open OpportunityDisparityCutset public

data OpportunityDisparityResidual : Set where
  populationFrameResidual opportunityResidual eligibilityResidual selectionResidual
  missingnessResidual opportunityDisparityClosed : OpportunityDisparityResidual

firstOpportunityDisparityResidual :
  OpportunityDisparityClaim → OpportunityDisparityCutset → OpportunityDisparityResidual
firstOpportunityDisparityResidual deploymentOpportunityDisparity c with populationFrameClosed c
... | false = populationFrameResidual
... | true with opportunityClosed c
...   | false = opportunityResidual
...   | true with missingnessClosed c
...     | false = missingnessResidual
...     | true = opportunityDisparityClosed
firstOpportunityDisparityResidual eligibilityConditionalDisparity c with opportunityClosed c
... | false = opportunityResidual
... | true with eligibilityClosed c
...   | false = eligibilityResidual
...   | true with missingnessClosed c
...     | false = missingnessResidual
...     | true = opportunityDisparityClosed
firstOpportunityDisparityResidual officerSelectionConditionalDisparity c with eligibilityClosed c
... | false = eligibilityResidual
... | true with selectionClosed c
...   | false = selectionResidual
...   | true with missingnessClosed c
...     | false = missingnessResidual
...     | true = opportunityDisparityClosed
firstOpportunityDisparityResidual unconditionalObservedDisparity c with populationFrameClosed c
... | false = populationFrameResidual
... | true with opportunityClosed c
...   | false = opportunityResidual
...   | true with eligibilityClosed c
...     | false = eligibilityResidual
...     | true with selectionClosed c
...       | false = selectionResidual
...       | true with missingnessClosed c
...         | false = missingnessResidual
...         | true = opportunityDisparityClosed

------------------------------------------------------------------------
-- Concrete separation witnesses.
------------------------------------------------------------------------

canonicalDeploymentOnlyCutset : OpportunityDisparityCutset
canonicalDeploymentOnlyCutset = opportunityDisparityCutset true true false false true
  "deployment opportunity measured; legal eligibility and conditional selection not yet measured"

canonicalDeploymentCanCloseBeforeSelection :
  firstOpportunityDisparityResidual deploymentOpportunityDisparity canonicalDeploymentOnlyCutset
  ≡ opportunityDisparityClosed
canonicalDeploymentCanCloseBeforeSelection = refl

canonicalOfficerSelectionStillNeedsEligibility :
  firstOpportunityDisparityResidual officerSelectionConditionalDisparity canonicalDeploymentOnlyCutset
  ≡ eligibilityResidual
canonicalOfficerSelectionStillNeedsEligibility = refl

record OpportunitySelectionBoundary : Set where
  constructor opportunitySelectionBoundary
  field
    geographicDeploymentDisparityEqualsOfficerSelectionDisparity : Bool
    geographicDeploymentDisparityEqualsOfficerSelectionDisparityIsFalse :
      geographicDeploymentDisparityEqualsOfficerSelectionDisparity ≡ false
    unconditionalSelectionRateIdentifiesConditionalOfficerSelection : Bool
    unconditionalSelectionRateIdentifiesConditionalOfficerSelectionIsFalse :
      unconditionalSelectionRateIdentifiesConditionalOfficerSelection ≡ false
    legalEligibilityEqualsExposureOpportunity : Bool
    legalEligibilityEqualsExposureOpportunityIsFalse :
      legalEligibilityEqualsExposureOpportunity ≡ false

canonicalOpportunitySelectionBoundary : OpportunitySelectionBoundary
canonicalOpportunitySelectionBoundary = opportunitySelectionBoundary false refl false refl false refl
