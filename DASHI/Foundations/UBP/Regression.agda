module DASHI.Foundations.UBP.Regression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Base using (_*_)
open import Data.Rational using (ℚ)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.EvidenceInterpretationLedger as Evidence
import DASHI.Foundations.UBP.ExactnessAndLatticeBoundary as Exactness
import DASHI.Foundations.UBP.ObservableAlgebraBoundary as Algebra
import DASHI.Foundations.UBP.RepresentationAndObserverBoundary as Representation
import DASHI.Foundations.UBP.SourceAtlas as Sources

------------------------------------------------------------------------
-- Focused aggregate for the UBP epistemic/lattice tranche.

sourceCountRegression :
  Sources.canonicalUBPSourceCount ≡ 7
sourceCountRegression =
  Sources.canonicalUBPSourceCountIsSeven

claimRowCountRegression :
  Evidence.canonicalUBPClaimRowCount ≡ 8
claimRowCountRegression =
  Evidence.canonicalUBPClaimRowCountIsEight

shadowCardinalityRegression :
  Representation.hexacodeShadowPreimageCount
  ≡
  Representation.shadowPreimageToGolayCardinalityRatio
    * Representation.golayCodewordCount
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
    (support Data.Rational.+ 1)
    (normSquared Data.Rational.+ coordinateSquare)
  Data.Rational.- Algebra.symmetryTax y support normSquared
  ≡
  Algebra.activationQuantum y coordinateSquare
activationDifferenceRegression =
  Algebra.activationDifferenceIdentity

longCycleCancellationRegression :
  (y : ℚ) →
  2 Data.Rational.* Algebra.activationQuantum y 1
  Data.Rational.+ 2 Data.Rational.* Algebra.deexcitationQuantum y 4
  ≡
  Data.Rational.0ℚ Data.Rational.- 3 Data.Rational./ 4
longCycleCancellationRegression =
  Algebra.longCycleCancellationIdentity

nrciHalfThresholdRegression :
  Algebra.nrci 10 ≡ 1 Data.Rational./ 2
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
  ∷ []

allFocusedReceiptsRemainNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsRemainNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
