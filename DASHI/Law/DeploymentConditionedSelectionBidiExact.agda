module DASHI.Law.DeploymentConditionedSelectionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.WandingOperationDeploymentProofExact as Deployment

------------------------------------------------------------------------
-- Claim-specific routing after deployment closure.
------------------------------------------------------------------------

data DeploymentSelectionClaim : Set where
  exposureOpportunityRate eligibleExposureRate conditionalSelectionRate
  deploymentAdjustedGroupDisparity : DeploymentSelectionClaim

data DeploymentSelectionProducer : Set where
  trafficObservationProducer exposureSetProducer eligibilityProducer
  selectionProducer groupLinkageProducer missingnessProducer : DeploymentSelectionProducer

reverseDeploymentSelection : DeploymentSelectionClaim → DeploymentSelectionProducer
reverseDeploymentSelection exposureOpportunityRate = exposureSetProducer
reverseDeploymentSelection eligibleExposureRate = eligibilityProducer
reverseDeploymentSelection conditionalSelectionRate = selectionProducer
reverseDeploymentSelection deploymentAdjustedGroupDisparity = groupLinkageProducer

record DeploymentSelectionCutset : Set where
  constructor deploymentSelectionCutset
  field
    deploymentClosed : Bool
    exposureSetClosed : Bool
    eligibilityClosed : Bool
    selectionClosed : Bool
    groupLinkageClosed : Bool
    missingnessClosed : Bool
    cutsetReference : String

open DeploymentSelectionCutset public

data DeploymentSelectionResidual : Set where
  deploymentResidual exposureSetResidual eligibilityResidual selectionResidual
  groupLinkageResidual missingnessResidual selectionClaimClosed : DeploymentSelectionResidual

firstDeploymentSelectionResidual :
  DeploymentSelectionClaim → DeploymentSelectionCutset → DeploymentSelectionResidual
firstDeploymentSelectionResidual exposureOpportunityRate c with deploymentClosed c
... | false = deploymentResidual
... | true with exposureSetClosed c
...   | false = exposureSetResidual
...   | true = selectionClaimClosed
firstDeploymentSelectionResidual eligibleExposureRate c with deploymentClosed c
... | false = deploymentResidual
... | true with exposureSetClosed c
...   | false = exposureSetResidual
...   | true with eligibilityClosed c
...     | false = eligibilityResidual
...     | true = selectionClaimClosed
firstDeploymentSelectionResidual conditionalSelectionRate c with deploymentClosed c
... | false = deploymentResidual
... | true with exposureSetClosed c
...   | false = exposureSetResidual
...   | true with eligibilityClosed c
...     | false = eligibilityResidual
...     | true with selectionClosed c
...       | false = selectionResidual
...       | true = selectionClaimClosed
firstDeploymentSelectionResidual deploymentAdjustedGroupDisparity c with deploymentClosed c
... | false = deploymentResidual
... | true with exposureSetClosed c
...   | false = exposureSetResidual
...   | true with eligibilityClosed c
...     | false = eligibilityResidual
...     | true with selectionClosed c
...       | false = selectionResidual
...       | true with groupLinkageClosed c
...         | false = groupLinkageResidual
...         | true with missingnessClosed c
...           | false = missingnessResidual
...           | true = selectionClaimClosed

canonicalExposureSetOpenCutset : DeploymentSelectionCutset
canonicalExposureSetOpenCutset = deploymentSelectionCutset
  true false false false false false
  "operation identified but eligible exposure set absent"

canonicalConditionalSelectionStopsAtExposureSet :
  firstDeploymentSelectionResidual conditionalSelectionRate canonicalExposureSetOpenCutset
  ≡ exposureSetResidual
canonicalConditionalSelectionStopsAtExposureSet = refl

canonicalAdjustedDisparityStopsAtGroupLinkage :
  firstDeploymentSelectionResidual deploymentAdjustedGroupDisparity
    (deploymentSelectionCutset true true true true false true
      "deployment/exposure/eligibility/selection closed; group linkage open")
  ≡ groupLinkageResidual
canonicalAdjustedDisparityStopsAtGroupLinkage = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record DeploymentSelectionBoundary : Set where
  constructor deploymentSelectionBoundary
  field
    operationAuthorisationClosesExposureDenominator : Bool
    operationAuthorisationClosesExposureDenominatorIsFalse :
      operationAuthorisationClosesExposureDenominator ≡ false
    exposureSetClosesSelectionRate : Bool
    exposureSetClosesSelectionRateIsFalse : exposureSetClosesSelectionRate ≡ false
    conditionalSelectionRateProvesDiscrimination : Bool
    conditionalSelectionRateProvesDiscriminationIsFalse :
      conditionalSelectionRateProvesDiscrimination ≡ false

canonicalDeploymentSelectionBoundary : DeploymentSelectionBoundary
canonicalDeploymentSelectionBoundary = deploymentSelectionBoundary false refl false refl false refl
