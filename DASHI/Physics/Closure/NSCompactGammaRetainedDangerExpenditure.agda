module DASHI.Physics.Closure.NSCompactGammaRetainedDangerExpenditure where

open import Agda.Primitive using (Set; Set₁)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

-- Positive-retention form of the danger-expenditure modulus.
-- `retain` is abstract and order preserving. A concrete real-number instance
-- may later supply the retention map derived from a local packet estimate.

record RetainedDangerExpenditureInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    MemberDanger : Set
    CenterBufferedDanger : Set

    centerLower : Scalar A
    memberLower : Scalar A
    centerEscape : Scalar A
    memberEscape : Scalar A

    retain : Scalar A → Scalar A

    dangerTransfersToBufferedCenter :
      MemberDanger → CenterBufferedDanger

    bufferedCenterDangerForcesEscape :
      CenterBufferedDanger →
      _≤_ A centerLower centerEscape

    retainMonotone :
      {left right : Scalar A} →
      _≤_ A left right →
      _≤_ A (retain left) (retain right)

    retainedCenterEscapeNearMember :
      _≤_ A (retain centerEscape) memberEscape

    memberLowerBelowRetainedCenterLower :
      _≤_ A memberLower (retain centerLower)

open RetainedDangerExpenditureInputs public

retainedDangerForcesMemberExpenditure :
  (A : AbsorptionArithmetic) →
  (I : RetainedDangerExpenditureInputs A) →
  MemberDanger I →
  _≤_ A (memberLower I) (memberEscape I)
retainedDangerForcesMemberExpenditure A I memberDanger =
  ≤-trans A
    (memberLowerBelowRetainedCenterLower I)
    (≤-trans A
      (retainMonotone I
        (bufferedCenterDangerForcesEscape I
          (dangerTransfersToBufferedCenter I memberDanger)))
      (retainedCenterEscapeNearMember I))
