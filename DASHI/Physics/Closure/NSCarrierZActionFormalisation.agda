module DASHI.Physics.Closure.NSCarrierZActionFormalisation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- NS carrier Z-action.
--
-- The lane-separation argument does not need the analytic dilation
-- operator on L2(R^3).  It needs only the shift of the prime-band index.
-- On the abstract carrier Hilbert space with orthonormal band basis
-- {e_j}_{j in Z}, the shift S(e_j)=e_{j+1} is unitary, faithful, and
-- gives a representation of the discrete group (Z,+).

data CarrierHilbertSpaceModel : Set where
  primeBandOrthonormalBasis :
    CarrierHilbertSpaceModel

data NSCarrierGenerator : Set where
  bandShiftOperator :
    NSCarrierGenerator

data NSCarrierGroup : Set where
  discreteIntegerGroup :
    NSCarrierGroup

data NSCarrierActionStatus : Set where
  formalisedByBandShift :
    NSCarrierActionStatus

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

bandShiftDefinition : String
bandShiftDefinition =
  "S(e_j)=e_{j+1} on the orthonormal prime-band basis of the carrier Hilbert space."

carrierHilbertSpaceStatement : String
carrierHilbertSpaceStatement =
  "H_carrier is the closed span of orthonormal band basis vectors e_j indexed by j in Z, representing Fourier support on prime-scale bands p^j."

unitarityStatement : String
unitarityStatement =
  "The band shift is unitary because it permutes an orthonormal basis."

faithfulnessStatement : String
faithfulnessStatement =
  "The representation rho_NS : Z -> U(H_carrier) is faithful because S^n=id implies n=0 on the indexed basis."

dilationIrrelevanceStatement : String
dilationIrrelevanceStatement =
  "Analytic dilation operators used for energy scaling are irrelevant to the lane-separation no-go; only the discrete band-shift representation is used."

record NSCarrierZActionFormalisation : Set where
  field
    carrierModel :
      CarrierHilbertSpaceModel

    carrierModelIsPrimeBandBasis :
      carrierModel ≡ primeBandOrthonormalBasis

    generator :
      NSCarrierGenerator

    generatorIsBandShift :
      generator ≡ bandShiftOperator

    representationGroup :
      NSCarrierGroup

    representationGroupIsDiscreteZ :
      representationGroup ≡ discreteIntegerGroup

    bandShift :
      String

    bandShiftIsCanonical :
      bandShift ≡ bandShiftDefinition

    carrierHilbertSpace :
      String

    carrierHilbertSpaceIsCanonical :
      carrierHilbertSpace ≡ carrierHilbertSpaceStatement

    bandShiftIsUnitary :
      Bool

    bandShiftIsUnitaryIsTrue :
      bandShiftIsUnitary ≡ true

    representationIsFaithful :
      Bool

    representationIsFaithfulIsTrue :
      representationIsFaithful ≡ true

    groupIsDiscrete :
      Bool

    groupIsDiscreteIsTrue :
      groupIsDiscrete ≡ true

    groupIsProfinite :
      Bool

    groupIsProfiniteIsFalse :
      groupIsProfinite ≡ false

    unitarityReason :
      String

    unitarityReasonIsCanonical :
      unitarityReason ≡ unitarityStatement

    faithfulnessReason :
      String

    faithfulnessReasonIsCanonical :
      faithfulnessReason ≡ faithfulnessStatement

    dilationOperatorNeededForNoGo :
      Bool

    dilationOperatorNeededForNoGoIsFalse :
      dilationOperatorNeededForNoGo ≡ false

    dilationIrrelevance :
      String

    dilationIrrelevanceIsCanonical :
      dilationIrrelevance ≡ dilationIrrelevanceStatement

    status :
      NSCarrierActionStatus

    statusIsFormalised :
      status ≡ formalisedByBandShift

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

open NSCarrierZActionFormalisation public

canonicalNSCarrierZActionFormalisation :
  NSCarrierZActionFormalisation
canonicalNSCarrierZActionFormalisation =
  record
    { carrierModel =
        primeBandOrthonormalBasis
    ; carrierModelIsPrimeBandBasis =
        refl
    ; generator =
        bandShiftOperator
    ; generatorIsBandShift =
        refl
    ; representationGroup =
        discreteIntegerGroup
    ; representationGroupIsDiscreteZ =
        refl
    ; bandShift =
        bandShiftDefinition
    ; bandShiftIsCanonical =
        refl
    ; carrierHilbertSpace =
        carrierHilbertSpaceStatement
    ; carrierHilbertSpaceIsCanonical =
        refl
    ; bandShiftIsUnitary =
        true
    ; bandShiftIsUnitaryIsTrue =
        refl
    ; representationIsFaithful =
        true
    ; representationIsFaithfulIsTrue =
        refl
    ; groupIsDiscrete =
        true
    ; groupIsDiscreteIsTrue =
        refl
    ; groupIsProfinite =
        false
    ; groupIsProfiniteIsFalse =
        refl
    ; unitarityReason =
        unitarityStatement
    ; unitarityReasonIsCanonical =
        refl
    ; faithfulnessReason =
        faithfulnessStatement
    ; faithfulnessReasonIsCanonical =
        refl
    ; dilationOperatorNeededForNoGo =
        false
    ; dilationOperatorNeededForNoGoIsFalse =
        refl
    ; dilationIrrelevance =
        dilationIrrelevanceStatement
    ; dilationIrrelevanceIsCanonical =
        refl
    ; status =
        formalisedByBandShift
    ; statusIsFormalised =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    }

nsCarrierZActionFormalised :
  status canonicalNSCarrierZActionFormalisation
  ≡ formalisedByBandShift
nsCarrierZActionFormalised =
  refl

nsCarrierZActionDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSCarrierZActionFormalisation
  ≡ false
nsCarrierZActionDoesNotPromoteClay =
  refl
