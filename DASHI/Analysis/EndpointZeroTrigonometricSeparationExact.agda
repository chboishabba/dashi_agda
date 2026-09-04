module DASHI.Analysis.EndpointZeroTrigonometricSeparationExact where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

import DASHI.Analysis.ConstructiveRealSpine as R
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Analysis.OrdinaryTranscendentalRealization as Trig

------------------------------------------------------------------------
-- EXACT ENDPOINT-ZERO ALGEBRA FOR A SEPARATED TRIGONOMETRIC MODE
--
-- mode(z) = A sin(k z) + B cos(k z)
--
-- At z=0, sin 0 = 0 and cos 0 = 1 force mode(0)=B.  Thus a zero
-- boundary condition at the first plate gives B=0.  The second plate then
-- reduces to the sine factor A sin(k d).
--
-- This does NOT classify all sine zeros and therefore does not by itself prove
-- k = n*pi/d.
------------------------------------------------------------------------

mode :
  {real : R.ConstructedOrderedCompleteReal} →
  {exp : R.ConstructedRealExponential real} →
  Trig.TrigonometricPowerSeriesAuthority real exp →
  R.Real real → R.Real real → R.Real real → R.Real real → R.Real real
mode {real} trig A B k z =
  R._+_ real
    (R._*_ real A (Trig.sin trig (R._*_ real k z)))
    (R._*_ real B (Trig.cos trig (R._*_ real k z)))

zeroTimes :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (x : R.Real real) →
  R._*_ real (R.zero real) x ≡ R.zero real
zeroTimes {real} laws x =
  trans
    (R.mulComm real (R.zero real) x)
    (Ring.mulZeroRightLaw laws x)

modeAtZeroIsCosineCoefficient :
  {real : R.ConstructedOrderedCompleteReal} →
  {exp : R.ConstructedRealExponential real} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (trig : Trig.TrigonometricPowerSeriesAuthority real exp) →
  (A B k : R.Real real) →
  mode trig A B k (R.zero real) ≡ B
modeAtZeroIsCosineCoefficient {real} laws trig A B k =
  trans
    (cong₂
      (R._+_ real)
      (cong
        (R._*_ real A)
        (trans
          (cong (Trig.sin trig) (Ring.mulZeroRightLaw laws k))
          (Trig.sinZero trig)))
      (cong
        (R._*_ real B)
        (trans
          (cong (Trig.cos trig) (Ring.mulZeroRightLaw laws k))
          (Trig.cosZero trig))))
    (trans
      (cong₂
        (R._+_ real)
        (Ring.mulZeroRightLaw laws A)
        (R.mulOneRight real B))
      (R.addZeroLeft real B))

firstEndpointZeroForcesCosineCoefficientZero :
  {real : R.ConstructedOrderedCompleteReal} →
  {exp : R.ConstructedRealExponential real} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (trig : Trig.TrigonometricPowerSeriesAuthority real exp) →
  (A B k : R.Real real) →
  mode trig A B k (R.zero real) ≡ R.zero real →
  B ≡ R.zero real
firstEndpointZeroForcesCosineCoefficientZero laws trig A B k boundary =
  trans
    (sym (modeAtZeroIsCosineCoefficient laws trig A B k))
    boundary

modeWithZeroCosineCoefficient :
  {real : R.ConstructedOrderedCompleteReal} →
  {exp : R.ConstructedRealExponential real} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (trig : Trig.TrigonometricPowerSeriesAuthority real exp) →
  (A k z : R.Real real) →
  mode trig A (R.zero real) k z
  ≡ R._*_ real A (Trig.sin trig (R._*_ real k z))
modeWithZeroCosineCoefficient {real} laws trig A k z =
  trans
    (cong₂
      (R._+_ real)
      refl
      (zeroTimes laws (Trig.cos trig (R._*_ real k z))))
    (R.addZeroRight real
      (R._*_ real A (Trig.sin trig (R._*_ real k z))))

record EndpointZeroReductionReceipt
    {real : R.ConstructedOrderedCompleteReal}
    {exp : R.ConstructedRealExponential real}
    (laws : Ring.ConstructedRealRingNormalisationLaws real)
    (trig : Trig.TrigonometricPowerSeriesAuthority real exp)
    (A B k d : R.Real real) : Set where
  field
    firstBoundaryZero : mode trig A B k (R.zero real) ≡ R.zero real
    secondBoundaryZero : mode trig A B k d ≡ R.zero real
    cosineCoefficientZero : B ≡ R.zero real
    secondBoundaryReducesToSineFactor :
      R._*_ real A (Trig.sin trig (R._*_ real k d)) ≡ R.zero real

open EndpointZeroReductionReceipt public

data EndpointReductionAutomaticallyClassifiesSineZeros : Set where

endpointAlgebraDoesNotClassifyAllZeros :
  EndpointReductionAutomaticallyClassifiesSineZeros → DASHI.Core.Prelude.⊥
endpointAlgebraDoesNotClassifyAllZeros ()
