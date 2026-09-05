module DASHI.Law.SelectionEligibilityDisparityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.CoerciveEncounterDenominatorIntegrityExact as Denom

------------------------------------------------------------------------
-- Eligibility and actual selection are distinct fibres.
------------------------------------------------------------------------

data GroupStatus : Set where
  groupRecorded groupNotRecorded groupMissing groupConflict : GroupStatus

data SelectionObservation : Set where
  eligibleObserved selectedObserved bothObserved observationMissing observationConflict : SelectionObservation

record SelectionEligibilityCell : Set where
  constructor selectionEligibilityCell
  field
    groupStatus : GroupStatus
    eligibility : Denom.EligibilityState
    selection : Denom.SelectionState
    cellReference : String

open SelectionEligibilityCell public

record DisparityCountSurface : Set where
  constructor disparityCountSurface
  field
    eligibleGroupCount selectedGroupCount : ℕ
    eligibleComparisonCount selectedComparisonCount : ℕ
    missingGroupStatusCount : ℕ
    repeatedPersonAdjustmentCount : ℕ
    denominatorReference : String

open DisparityCountSurface public

------------------------------------------------------------------------
-- The observed scan share and the selection-rate estimand are different.
------------------------------------------------------------------------

data DisparityEstimand : Set where
  scanShare selectionRateByGroup selectionRateRatio selectionRateDifference : DisparityEstimand

record DisparityRatioRequest : Set where
  constructor disparityRatioRequest
  field
    estimand : DisparityEstimand
    groupNumerator groupDenominator : ℕ
    comparisonNumerator comparisonDenominator : ℕ
    groupNumeratorMeaning groupDenominatorMeaning : String
    comparisonNumeratorMeaning comparisonDenominatorMeaning : String
    missingnessReference : String

open DisparityRatioRequest public

selectionRateRequest : DisparityCountSurface → DisparityRatioRequest
selectionRateRequest s = disparityRatioRequest
  selectionRateByGroup
  (selectedGroupCount s)
  (eligibleGroupCount s)
  (selectedComparisonCount s)
  (eligibleComparisonCount s)
  "selected members of target group"
  "eligible members of target group"
  "selected members of comparison population"
  "eligible members of comparison population"
  (denominatorReference s)

------------------------------------------------------------------------
-- BIDI: a disparity claim routes backwards to eligibility, selection, linkage,
-- and missingness producers, not merely a population census share.
------------------------------------------------------------------------

data DisparityClaim : Set where
  descriptiveScanShare descriptiveSelectionDisparity causalDiscrimination : DisparityClaim

data DisparityProducer : Set where
  scanCountProducer eligibilityDenominatorProducer selectionProducer
  personLinkageProducer missingStatusProducer causalSelectionModelProducer : DisparityProducer

reverseDisparity : DisparityClaim → DisparityProducer
reverseDisparity descriptiveScanShare = scanCountProducer
reverseDisparity descriptiveSelectionDisparity = eligibilityDenominatorProducer
reverseDisparity causalDiscrimination = causalSelectionModelProducer

record SelectionDisparityCutset : Set where
  constructor selectionDisparityCutset
  field
    scanCountsClosed : Bool
    eligibilityClosed : Bool
    selectionClosed : Bool
    personLinkageClosed : Bool
    missingStatusClosed : Bool
    causalModelClosed : Bool
    cutsetReference : String

open SelectionDisparityCutset public

data DisparityResidual : Set where
  scanCountResidual eligibilityResidual selectionResidual linkageResidual
  missingStatusResidual causalModelResidual disparityClosed : DisparityResidual

firstDisparityResidual : DisparityClaim → SelectionDisparityCutset → DisparityResidual
firstDisparityResidual descriptiveScanShare c with scanCountsClosed c
... | false = scanCountResidual
... | true = disparityClosed
firstDisparityResidual descriptiveSelectionDisparity c with eligibilityClosed c
... | false = eligibilityResidual
... | true with selectionClosed c
...   | false = selectionResidual
...   | true with personLinkageClosed c
...     | false = linkageResidual
...     | true with missingStatusClosed c
...       | false = missingStatusResidual
...       | true = disparityClosed
firstDisparityResidual causalDiscrimination c with eligibilityClosed c
... | false = eligibilityResidual
... | true with selectionClosed c
...   | false = selectionResidual
...   | true with personLinkageClosed c
...     | false = linkageResidual
...     | true with missingStatusClosed c
...       | false = missingStatusResidual
...       | true with causalModelClosed c
...         | false = causalModelResidual
...         | true = disparityClosed

canonicalScanShareOnly : SelectionDisparityCutset
canonicalScanShareOnly = selectionDisparityCutset true false true false false false
  "scan counts exist but eligibility, linkage and missingness remain open"

scanShareDoesNotCloseSelectionDisparity :
  firstDisparityResidual descriptiveSelectionDisparity canonicalScanShareOnly ≡ eligibilityResidual
scanShareDoesNotCloseSelectionDisparity = refl

causalClaimRequiresCausalModel :
  firstDisparityResidual causalDiscrimination
    (selectionDisparityCutset true true true true true false "descriptive selection surface closed")
  ≡ causalModelResidual
causalClaimRequiresCausalModel = refl

record SelectionDisparityBoundary : Set where
  constructor selectionDisparityBoundary
  field
    populationShareIsEligibilityDenominator : Bool
    populationShareIsEligibilityDenominatorIsFalse : populationShareIsEligibilityDenominator ≡ false
    scanShareProvesSelectionDisparity : Bool
    scanShareProvesSelectionDisparityIsFalse : scanShareProvesSelectionDisparity ≡ false
    selectionDisparityProvesCausalDiscrimination : Bool
    selectionDisparityProvesCausalDiscriminationIsFalse : selectionDisparityProvesCausalDiscrimination ≡ false

canonicalSelectionDisparityBoundary : SelectionDisparityBoundary
canonicalSelectionDisparityBoundary = selectionDisparityBoundary false refl false refl false refl
