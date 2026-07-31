module DASHI.Foundations.UBP.Regression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Nat.Base as Nat
open import Data.Rational using (ℚ; _+_; _-_; _*_; 0ℚ)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.EvidenceInterpretationLedger as Evidence
import DASHI.Foundations.UBP.ExactnessAndLatticeBoundary as Exactness
import DASHI.Foundations.UBP.ObservableAlgebraBoundary as Algebra
import DASHI.Foundations.UBP.Pi50ConvergentTable as Pi50
import DASHI.Foundations.UBP.RepresentationAndObserverBoundary as Representation
import DASHI.Foundations.UBP.SourceAtlas as Sources

------------------------------------------------------------------------
-- Focused aggregate for the UBP epistemic/lattice tranche.
------------------------------------------------------------------------

sourceCountRegression :
  Sources.canonicalUBPSourceCount ≡ 8
sourceCountRegression =
  Sources.canonicalUBPSourceCountIsEight

claimRowCountRegression :
  Evidence.canonicalUBPClaimRowCount ≡ 8
claimRowCountRegression =
  Evidence.canonicalUBPClaimRowCountIsEight

shadowCardinalityRegression :
  Representation.hexacodeShadowPreimageCount
  ≡
  Nat._*_
    Representation.shadowPreimageToGolayCardinalityRatio
    Representation.golayCodewordCount
shadowCardinalityRegression =
  Representation.shadowPreimageCountIsSixtyFourTimesGolayCount

observerConstantFractionClaimClosed :
  Exactness.exactIrrationalTargetRepresentedByFraction
    Exactness.canonicalObserverConstantStatus
  ≡
  false
observerConstantFractionClaimClosed =
  Exactness.exactIrrationalTargetRepresentedByFractionIsFalse
    Exactness.canonicalObserverConstantStatus

ambientAddressMembershipClaimClosed :
  Exactness.individualAddressMembershipClaim
    Exactness.canonicalAmbientAddressStatus
  ≡
  false
ambientAddressMembershipClaimClosed =
  Exactness.individualAddressMembershipClaimIsFalse
    Exactness.canonicalAmbientAddressStatus

activationDifferenceRegression :
  (y support normSquared coordinateSquare : ℚ) →
  Algebra.symmetryTax
    y
    (support + 1)
    (normSquared + coordinateSquare)
  - Algebra.symmetryTax y support normSquared
  ≡
  Algebra.activationQuantum y coordinateSquare
activationDifferenceRegression =
  Algebra.activationDifferenceIdentity

longCycleCancellationRegression :
  (y : ℚ) →
  2 * Algebra.activationQuantum y 1
  + 2 * Algebra.deexcitationQuantum y 4
  ≡
  0ℚ - Algebra.threeQuarters
longCycleCancellationRegression =
  Algebra.longCycleCancellationIdentity

nrciHalfThresholdRegression :
  Algebra.nrci 10 ≡ Algebra.oneHalf
nrciHalfThresholdRegression =
  Algebra.nrciAtTaxTen

nrciPhysicalEmergenceClaimClosed :
  Algebra.independentlyEmergentPhysicalThresholdEstablished
    Algebra.canonicalCoherenceThresholdStatus
  ≡
  false
nrciPhysicalEmergenceClaimClosed =
  Algebra.independentlyEmergentPhysicalThresholdEstablishedIsFalse
    Algebra.canonicalCoherenceThresholdStatus

mogEquivalenceClaimClosed :
  Representation.checkAloneProvesEquivalence
    Representation.canonicalMOGHexacodeStatus
  ≡
  false
mogEquivalenceClaimClosed =
  Representation.checkAloneProvesEquivalenceIsFalse
    Representation.canonicalMOGHexacodeStatus

coordinateMassMeaningClosed :
  Representation.intrinsicMassMeaningEstablished
    Representation.canonicalCoordinateInterpretationStatus
  ≡
  false
coordinateMassMeaningClosed =
  Representation.intrinsicMassMeaningEstablishedIsFalse
    Representation.canonicalCoordinateInterpretationStatus

graySemanticAutomaticityClosed :
  Representation.semanticEncodingConstructedByIsometryAlone
    Representation.canonicalGraySemanticStatus
  ≡
  false
graySemanticAutomaticityClosed =
  Representation.semanticEncodingConstructedByIsometryAloneIsFalse
    Representation.canonicalGraySemanticStatus

leechToThreeDimensionalProjectionClaimClosed :
  Representation.genuineLeechToThreeDimensionalProjectionSupplied
    Representation.canonicalSpatialCodecStatus
  ≡
  false
leechToThreeDimensionalProjectionClaimClosed =
  Representation.genuineLeechToThreeDimensionalProjectionSuppliedIsFalse
    Representation.canonicalSpatialCodecStatus

externalReplicationClaimClosed :
  Evidence.externalReplicationSupplied
    Evidence.canonicalInterpretationBoundaryStatus
  ≡
  false
externalReplicationClaimClosed =
  Evidence.externalReplicationSuppliedIsFalse
    Evidence.canonicalInterpretationBoundaryStatus

sourcePiTableCanonicalClaimClosed :
  Pi50.sourceTableIsCanonicalPiCFThrough50
    Pi50.canonicalPi50TableStatus
  ≡ false
sourcePiTableCanonicalClaimClosed =
  Pi50.sourceTableIsCanonicalPiCFThrough50IsFalse
    Pi50.canonicalPi50TableStatus

sourcePiCoefficient48Regression :
  Pi50.sourceCoefficient48 ≡ 6
sourcePiCoefficient48Regression =
  Pi50.sourceCoefficient48IsSix

canonicalPiCoefficient48Regression :
  Pi50.canonicalCoefficient48 ≡ 2
canonicalPiCoefficient48Regression =
  Pi50.canonicalCoefficient48IsTwo

sourceP50Regression :
  Pi50.sourceP50 ≡
    183157143516396120473427579101
sourceP50Regression =
  Pi50.sourceP50Exact

canonicalP50Regression :
  Pi50.canonicalP50 ≡
    16397605394050964443746106649
canonicalP50Regression =
  Pi50.canonicalP50Exact

canonicalQ50Regression :
  Pi50.canonicalQ50 ≡
    5219519906667074477262822481
canonicalQ50Regression =
  Pi50.canonicalQ50Exact

allEvidenceRowsRemainNonPromoting :
  Evidence.AllClaimRowsNonPromoting Evidence.canonicalUBPClaimRows
allEvidenceRowsRemainNonPromoting =
  Evidence.canonicalUBPClaimRowsNonPromoting

focusedReceipts :
  List GenericReceipt.GenericReceipt
focusedReceipts =
  Sources.canonicalUBPSourceReceipt
  ∷ Exactness.ubpExactnessAndLatticeReceipt
  ∷ Algebra.observableAlgebraReceipt
  ∷ Representation.representationAndObserverReceipt
  ∷ Evidence.ubpInterpretationGenericReceipt
  ∷ Pi50.pi50GenericReceipt
  ∷ []

allFocusedReceiptsRemainNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsRemainNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
