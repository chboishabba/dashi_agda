module DASHI.Foundations.UBP.Regression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Base using (_*_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.EvidenceInterpretationLedger as Evidence
import DASHI.Foundations.UBP.ExactnessAndLatticeBoundary as Exactness
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
  ∷ Representation.representationAndObserverReceipt
  ∷ Evidence.ubpInterpretationGenericReceipt
  ∷ []

allFocusedReceiptsRemainNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsRemainNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
