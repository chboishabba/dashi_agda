module DASHI.Law.PartialIdentificationMissingnessBoundsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Partial identification: missing observations produce admissible intervals,
-- not imputed point estimates.
------------------------------------------------------------------------

record CountBounds : Set where
  constructor countBounds
  field
    lower upper : ℕ
    boundMeaning : String
    boundReference : String

open CountBounds public

record MissingMassSurface : Set where
  constructor missingMassSurface
  field
    observedPositive : ℕ
    observedNegative : ℕ
    missing : ℕ
    conflict : ℕ
    surfaceReference : String

open MissingMassSurface public

positiveCountBounds : MissingMassSurface → CountBounds
positiveCountBounds s = countBounds
  (observedPositive s)
  (observedPositive s + missing s + conflict s)
  "true positive count lies between observed positives and all unresolved mass allocated positive"
  (surfaceReference s)

record RatioBounds : Set where
  constructor ratioBounds
  field
    numeratorLower numeratorUpper : ℕ
    denominatorLower denominatorUpper : ℕ
    ratioMeaning : String
    ratioReference : String

open RatioBounds public

record SelectionMissingnessSurface : Set where
  constructor selectionMissingnessSurface
  field
    selectedObserved : ℕ
    selectedStatusMissing : ℕ
    eligibleObserved : ℕ
    eligibleStatusMissing : ℕ
    linkageUnresolved : ℕ
    exposureUnresolved : ℕ
    selectionReference : String

open SelectionMissingnessSurface public

selectionRateBounds : SelectionMissingnessSurface → RatioBounds
selectionRateBounds s = ratioBounds
  (selectedObserved s)
  (selectedObserved s + selectedStatusMissing s + linkageUnresolved s)
  (eligibleObserved s)
  (eligibleObserved s + eligibleStatusMissing s + linkageUnresolved s + exposureUnresolved s)
  "selection-rate identified set under worst-case allocation of unresolved group/linkage/exposure mass"
  (selectionReference s)

------------------------------------------------------------------------
-- Robust disparity status.  We compare cross-multiplied count bounds only in
-- theorem-shaped witnesses below; no floating-point division is introduced.
------------------------------------------------------------------------

data IdentificationStatus : Set where
  disparityRobustPositive disparityRobustNegative disparityNotIdentified : IdentificationStatus

record TwoGroupRateBounds : Set where
  constructor twoGroupRateBounds
  field
    groupA : RatioBounds
    groupB : RatioBounds
    comparisonReference : String

open TwoGroupRateBounds public

------------------------------------------------------------------------
-- BIDI: stronger claims require stronger missingness closure.
------------------------------------------------------------------------

data MissingnessClaim : Set where
  boundedGroupCount boundedSelectionRate robustSelectionDisparity pointIdentifiedSelectionRate : MissingnessClaim

data MissingnessProducer : Set where
  unresolvedMassCount selectionEligibilityBounds worstCaseAllocationProof completeStatusObservation : MissingnessProducer

reverseMissingness : MissingnessClaim → MissingnessProducer
reverseMissingness boundedGroupCount = unresolvedMassCount
reverseMissingness boundedSelectionRate = selectionEligibilityBounds
reverseMissingness robustSelectionDisparity = worstCaseAllocationProof
reverseMissingness pointIdentifiedSelectionRate = completeStatusObservation

record MissingnessCutset : Set where
  constructor missingnessCutset
  field
    unresolvedMassClosed : Bool
    selectionEligibilityBoundsClosed : Bool
    worstCaseAllocationClosed : Bool
    completeObservationClosed : Bool
    cutsetReference : String

open MissingnessCutset public

data MissingnessResidual : Set where
  unresolvedMassResidual boundsResidual worstCaseResidual completeObservationResidual missingnessClosed : MissingnessResidual

firstMissingnessResidual : MissingnessClaim → MissingnessCutset → MissingnessResidual
firstMissingnessResidual boundedGroupCount c with unresolvedMassClosed c
... | false = unresolvedMassResidual
... | true = missingnessClosed
firstMissingnessResidual boundedSelectionRate c with unresolvedMassClosed c
... | false = unresolvedMassResidual
... | true with selectionEligibilityBoundsClosed c
...   | false = boundsResidual
...   | true = missingnessClosed
firstMissingnessResidual robustSelectionDisparity c with unresolvedMassClosed c
... | false = unresolvedMassResidual
... | true with selectionEligibilityBoundsClosed c
...   | false = boundsResidual
...   | true with worstCaseAllocationClosed c
...     | false = worstCaseResidual
...     | true = missingnessClosed
firstMissingnessResidual pointIdentifiedSelectionRate c with completeObservationClosed c
... | false = completeObservationResidual
... | true = missingnessClosed

------------------------------------------------------------------------
-- Canonical bounds witnesses.
------------------------------------------------------------------------

canonicalGroupSurface : MissingMassSurface
canonicalGroupSurface = missingMassSurface 11 50 39 0
  "illustrative percentage-like count surface only; not a real QPS microdataset"

canonicalGroupLower : lower (positiveCountBounds canonicalGroupSurface) ≡ 11
canonicalGroupLower = refl

canonicalGroupUpper : upper (positiveCountBounds canonicalGroupSurface) ≡ 50
canonicalGroupUpper = refl

canonicalSelectionSurface : SelectionMissingnessSurface
canonicalSelectionSurface = selectionMissingnessSurface 12 4 40 8 2 3
  "synthetic selection-rate missingness surface"

canonicalSelectionNumeratorLower :
  numeratorLower (selectionRateBounds canonicalSelectionSurface) ≡ 12
canonicalSelectionNumeratorLower = refl

canonicalSelectionNumeratorUpper :
  numeratorUpper (selectionRateBounds canonicalSelectionSurface) ≡ 18
canonicalSelectionNumeratorUpper = refl

canonicalSelectionDenominatorLower :
  denominatorLower (selectionRateBounds canonicalSelectionSurface) ≡ 40
canonicalSelectionDenominatorLower = refl

canonicalSelectionDenominatorUpper :
  denominatorUpper (selectionRateBounds canonicalSelectionSurface) ≡ 53
canonicalSelectionDenominatorUpper = refl

canonicalBoundedButNotPointIdentified : MissingnessCutset
canonicalBoundedButNotPointIdentified = missingnessCutset true true true false
  "bounds and worst-case allocation close, but complete observation remains open"

pointEstimateStillBlockedByMissingness :
  firstMissingnessResidual pointIdentifiedSelectionRate canonicalBoundedButNotPointIdentified
  ≡ completeObservationResidual
pointEstimateStillBlockedByMissingness = refl

robustDisparityCanCloseWithoutPointIdentification :
  firstMissingnessResidual robustSelectionDisparity canonicalBoundedButNotPointIdentified
  ≡ missingnessClosed
robustDisparityCanCloseWithoutPointIdentification = refl

record PartialIdentificationBoundary : Set where
  constructor partialIdentificationBoundary
  field
    missingMassMayBeSilentlyImputed : Bool
    missingMassMayBeSilentlyImputedIsFalse : missingMassMayBeSilentlyImputed ≡ false
    intervalBoundEqualsPointEstimate : Bool
    intervalBoundEqualsPointEstimateIsFalse : intervalBoundEqualsPointEstimate ≡ false
    robustDisparityRequiresCompleteObservation : Bool
    robustDisparityRequiresCompleteObservationIsFalse : robustDisparityRequiresCompleteObservation ≡ false

canonicalPartialIdentificationBoundary : PartialIdentificationBoundary
canonicalPartialIdentificationBoundary = partialIdentificationBoundary false refl false refl false refl
