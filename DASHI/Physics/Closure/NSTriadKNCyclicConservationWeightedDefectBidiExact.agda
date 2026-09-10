module DASHI.Physics.Closure.NSTriadKNCyclicConservationWeightedDefectBidiExact where

------------------------------------------------------------------------
-- THREE-LEG CONSERVATION TURNS WEIGHTED SUM INTO WEIGHT DEFECTS
--
-- The existing weighted Fourier-energy owner carries a fully symmetric
-- multiplier-difference presentation with a 1/3 normalization seam.  R503 does
-- not need that stronger presentation.  If a three-leg transfer satisfies
--
--   T2 = -(T0 + T1),
--
-- then finite rational algebra gives the least-privilege identity
--
--   w0*T0 + w1*T1 + w2*T2
--     = (w0-w2)*T0 + (w1-w2)*T1.
--
-- Thus exact unweighted cyclic cancellation need not survive the R503 weight.
-- Its failure to descend is precisely measured by two weight defects.  The
-- companion cyclic-resolvent owner then factors each such defect through a
-- radial pair-rate difference.
--
-- This module deliberately does NOT assert that the R503 oriented force terms
-- are the three conserved modal-transfer legs.  That same-object weld remains
-- the next prerequisite.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record CyclicTransferTriple : Set where
  constructor cyclic-transfer-triple
  field
    T0 T1 T2 : ℚ
    thirdFromConservation : T2 ≡ 0ℚ - (T0 + T1)

open CyclicTransferTriple public

weightedCyclicSum : ℚ → ℚ → ℚ → CyclicTransferTriple → ℚ
weightedCyclicSum w0 w1 w2 T =
  w0 * T0 T + w1 * T1 T + w2 * T2 T

twoDefectForm : ℚ → ℚ → ℚ → CyclicTransferTriple → ℚ
twoDefectForm w0 w1 w2 T =
  (w0 - w2) * T0 T + (w1 - w2) * T1 T

weightedCyclicSumIsTwoDefects :
  (w0 w1 w2 : ℚ) →
  (T : CyclicTransferTriple) →
  weightedCyclicSum w0 w1 w2 T ≡ twoDefectForm w0 w1 w2 T
weightedCyclicSumIsTwoDefects w0 w1 w2 T =
  let
    t0 = T0 T
    t1 = T1 T
    t2 = T2 T

    replaceThird :
      weightedCyclicSum w0 w1 w2 T
      ≡ w0 * t0 + w1 * t1 + w2 * (0ℚ - (t0 + t1))
    replaceThird =
      cong
        (λ selected → w0 * t0 + w1 * t1 + w2 * selected)
        (thirdFromConservation T)
  in
  trans replaceThird (solve (w0 ∷ w1 ∷ w2 ∷ t0 ∷ t1 ∷ []))

-- Choosing any common reference weight c gives an equivalent defect-only
-- presentation.  The w2 choice above is merely the two-term minimal form.
commonWeightCancels :
  (c : ℚ) →
  (T : CyclicTransferTriple) →
  c * T0 T + c * T1 T + c * T2 T ≡ 0ℚ
commonWeightCancels c T =
  let
    t0 = T0 T
    t1 = T1 T
    t2 = T2 T
    replaceThird :
      c * t0 + c * t1 + c * t2
      ≡ c * t0 + c * t1 + c * (0ℚ - (t0 + t1))
    replaceThird =
      cong (λ selected → c * t0 + c * t1 + c * selected)
        (thirdFromConservation T)
  in
  trans replaceThird (solve (c ∷ t0 ∷ t1 ∷ []))

------------------------------------------------------------------------
-- Boundary / proof-search state.
------------------------------------------------------------------------

weightedCyclicSumNeedsWeightInvariance : Bool
weightedCyclicSumNeedsWeightInvariance = false

constantWeightPartCancelsExactly : Bool
constantWeightPartCancelsExactly = true

weightedResidualUsesOnlyTwoWeightDefects : Bool
weightedResidualUsesOnlyTwoWeightDefects = true

oneThirdNormalizationRequired : Bool
oneThirdNormalizationRequired = false

r503OrientedTermsIdentifiedWithConservedThreeLegTransfer : Bool
r503OrientedTermsIdentifiedWithConservedThreeLegTransfer = false

r503WeightedCyclicPaymentClosed : Bool
r503WeightedCyclicPaymentClosed = false

clayPromotion : Bool
clayPromotion = false

weightedCyclicSumNeedsWeightInvarianceIsFalse :
  weightedCyclicSumNeedsWeightInvariance ≡ false
weightedCyclicSumNeedsWeightInvarianceIsFalse = refl

constantWeightPartCancelsExactlyIsTrue :
  constantWeightPartCancelsExactly ≡ true
constantWeightPartCancelsExactlyIsTrue = refl

oneThirdNormalizationRequiredIsFalse :
  oneThirdNormalizationRequired ≡ false
oneThirdNormalizationRequiredIsFalse = refl

r503OrientedTermsIdentifiedWithConservedThreeLegTransferIsFalse :
  r503OrientedTermsIdentifiedWithConservedThreeLegTransfer ≡ false
r503OrientedTermsIdentifiedWithConservedThreeLegTransferIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
