module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact where

------------------------------------------------------------------------
-- S2b2d1b2 / COHERENT WORK DIFFERENCE = WORK AGAINST VECTOR DIFFERENCE
--
-- The open coherent-covariance numerator contains
--
--   (r_i-r_j)(w_i-w_j),
--
-- with
--
--   w_i = 2 Re <M,A_i>.
--
-- The scalar work difference is not an independent state quantity:
--
--   w_i-w_j = 2 Re <M,A_i-A_j>.
--
-- This owner proves that identity on the literal rational Complex3 carrier and
-- immediately applies the existing Hermitian Young theorem:
--
--   |w_i-w_j|
--      <= 2 ( ||M||^2 + ||A_i-A_j||^2 ).
--
-- Thus d1b2 reduces to rate-difference weighting of an already-owned vector
-- pair-difference mass; no new "G1 state amplitude" oracle is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

coherentWorkDifferenceIsVectorDifference :
  (mixed left right : C3.Complex3 F) →
  Work.coherentWork mixed left - Work.coherentWork mixed right
  ≡ Work.coherentWork mixed (C3.complex3Subtract left right)
coherentWorkDifferenceIsVectorDifference
    (C3.complex3
      (C3.complex mx mxi)
      (C3.complex my myi)
      (C3.complex mz mzi))
    (C3.complex3
      (C3.complex ax axi)
      (C3.complex ay ayi)
      (C3.complex az azi))
    (C3.complex3
      (C3.complex bx bxi)
      (C3.complex by byi)
      (C3.complex bz bzi)) =
  solve
    ( mx ∷ mxi ∷ my ∷ myi ∷ mz ∷ mzi
    ∷ ax ∷ axi ∷ ay ∷ ayi ∷ az ∷ azi
    ∷ bx ∷ bxi ∷ by ∷ byi ∷ bz ∷ bzi
    ∷ [] )

coherentWorkDifferenceMagnitude :
  (mixed left right : C3.Complex3 F) →
  ∣ Work.coherentWork mixed left - Work.coherentWork mixed right ∣
  ≡
  two * ∣ R179.realHermitianCross
      mixed (C3.complex3Subtract left right) ∣
coherentWorkDifferenceMagnitude mixed left right =
  let
    cross =
      R179.realHermitianCross mixed
        (C3.complex3Subtract left right)

    twoNN : 0ℚ ≤ two
    twoNN = ℚP.+-mono-≤ ℚP.≤-refl ℚP.≤-refl
  in
  trans
    (cong ∣_∣
      (coherentWorkDifferenceIsVectorDifference mixed left right))
    (trans
      (ℚP.∣p*q∣≡∣p∣*∣q∣ two cross)
      (cong (_* ∣ cross ∣)
        (ℚP.0≤p⇒∣p∣≡p twoNN)))

coherentWorkDifferenceMagnitudeBound :
  (mixed left right : C3.Complex3 F) →
  ∣ Work.coherentWork mixed left - Work.coherentWork mixed right ∣
  ≤
  two *
    (L2.complex3NormSquared mixed
      + L2.complex3NormSquared (C3.complex3Subtract left right))
coherentWorkDifferenceMagnitudeBound mixed left right =
  let
    difference = C3.complex3Subtract left right
    local :
      ∣ R179.realHermitianCross mixed difference ∣
      ≤ L2.complex3NormSquared mixed + L2.complex3NormSquared difference
    local = R579.rationalRealHermitianYoung mixed difference

    scaled :
      two * ∣ R179.realHermitianCross mixed difference ∣
      ≤
      two *
        (L2.complex3NormSquared mixed
          + L2.complex3NormSquared difference)
    scaled = ℚP.*-monoˡ-≤-nonNeg two local
  in
  subst
    (λ lower →
      lower
      ≤ two *
        (L2.complex3NormSquared mixed
          + L2.complex3NormSquared difference))
    (sym (coherentWorkDifferenceMagnitude mixed left right))
    scaled

fixedOutputWorkDifferenceVectorBridgeClosed : Bool
fixedOutputWorkDifferenceVectorBridgeClosed = true

fixedOutputWorkDifferenceYoungBoundClosed : Bool
fixedOutputWorkDifferenceYoungBoundClosed = true

independentScalarStateDifferenceOracleRequired : Bool
independentScalarStateDifferenceOracleRequired = false

quantitativeRateWeightedFamilyPaymentClosedHere : Bool
quantitativeRateWeightedFamilyPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

fixedOutputWorkDifferenceVectorBridgeClosedIsTrue :
  fixedOutputWorkDifferenceVectorBridgeClosed ≡ true
fixedOutputWorkDifferenceVectorBridgeClosedIsTrue = refl

fixedOutputWorkDifferenceYoungBoundClosedIsTrue :
  fixedOutputWorkDifferenceYoungBoundClosed ≡ true
fixedOutputWorkDifferenceYoungBoundClosedIsTrue = refl

independentScalarStateDifferenceOracleRequiredIsFalse :
  independentScalarStateDifferenceOracleRequired ≡ false
independentScalarStateDifferenceOracleRequiredIsFalse = refl

quantitativeRateWeightedFamilyPaymentClosedHereIsFalse :
  quantitativeRateWeightedFamilyPaymentClosedHere ≡ false
quantitativeRateWeightedFamilyPaymentClosedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
