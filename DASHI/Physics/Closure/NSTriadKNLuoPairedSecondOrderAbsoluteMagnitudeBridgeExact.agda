module DASHI.Physics.Closure.NSTriadKNLuoPairedSecondOrderAbsoluteMagnitudeBridgeExact where

------------------------------------------------------------------------
-- GENERIC AUG-5 BRIDGE: SIGNED SECOND-ORDER DEFECT -> NONNEGATIVE MAGNITUDE
--
-- The existing paired second-order identity keeps
--
--   w [ L (g+ - g-) + R+ g+ + R- g- ]
--
-- signed.  The existing PairedSecondMomentSample expects the corresponding
-- nonnegative magnitudes.  This owner proves the least-privilege bridge by
-- taking absolute values only AFTER the signed second-order identity.
--
-- No Taylor-envelope, shell, six-three, cutoff, spacetime or PDE estimate is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondOrderExact as Second
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

absoluteMagnitudeSample :
  (displacement : ℚ) →
  0ℚ ≤ displacement →
  Second.PairedCommutatorSample →
  Moment.PairedSecondMomentSample
absoluteMagnitudeSample displacement displacementNN sample =
  Moment.paired-second-moment-sample
    ∣ Second.weight sample ∣
    displacement
    ∣ Second.linearIncrement sample ∣
    ∣ Second.plusDerivative sample - Second.minusDerivative sample ∣
    ∣ Second.plusRemainder sample ∣
    ∣ Second.minusRemainder sample ∣
    ∣ Second.plusDerivative sample ∣
    ∣ Second.minusDerivative sample ∣
    (ℚP.0≤∣p∣ (Second.weight sample))
    displacementNN
    (ℚP.0≤∣p∣ (Second.linearIncrement sample))
    (ℚP.0≤∣p∣
      (Second.plusDerivative sample - Second.minusDerivative sample))
    (ℚP.0≤∣p∣ (Second.plusRemainder sample))
    (ℚP.0≤∣p∣ (Second.minusRemainder sample))
    (ℚP.0≤∣p∣ (Second.plusDerivative sample))
    (ℚP.0≤∣p∣ (Second.minusDerivative sample))

innerSigned : Second.PairedCommutatorSample → ℚ
innerSigned sample =
  Second.linearIncrement sample
    * (Second.plusDerivative sample - Second.minusDerivative sample)
  + Second.plusRemainder sample * Second.plusDerivative sample
  + Second.minusRemainder sample * Second.minusDerivative sample

innerAbsoluteEnvelope : Second.PairedCommutatorSample → ℚ
innerAbsoluteEnvelope sample =
  ∣ Second.linearIncrement sample ∣
    * ∣ Second.plusDerivative sample - Second.minusDerivative sample ∣
  + ∣ Second.plusRemainder sample ∣ * ∣ Second.plusDerivative sample ∣
  + ∣ Second.minusRemainder sample ∣ * ∣ Second.minusDerivative sample ∣

innerSignedAbsoluteBelowEnvelope :
  (sample : Second.PairedCommutatorSample) →
  ∣ innerSigned sample ∣ ≤ innerAbsoluteEnvelope sample
innerSignedAbsoluteBelowEnvelope sample =
  let
    linearTerm =
      Second.linearIncrement sample
        * (Second.plusDerivative sample - Second.minusDerivative sample)
    plusTerm = Second.plusRemainder sample * Second.plusDerivative sample
    minusTerm = Second.minusRemainder sample * Second.minusDerivative sample

    firstTriangle :
      ∣ (linearTerm + plusTerm) + minusTerm ∣
      ≤ ∣ linearTerm + plusTerm ∣ + ∣ minusTerm ∣
    firstTriangle =
      ℚP.∣p+q∣≤∣p∣+∣q∣ (linearTerm + plusTerm) minusTerm

    secondTriangle :
      ∣ linearTerm + plusTerm ∣ + ∣ minusTerm ∣
      ≤ (∣ linearTerm ∣ + ∣ plusTerm ∣) + ∣ minusTerm ∣
    secondTriangle =
      ℚP.+-mono-≤
        (ℚP.∣p+q∣≤∣p∣+∣q∣ linearTerm plusTerm)
        ℚP.≤-refl

    triangle :
      ∣ innerSigned sample ∣
      ≤ (∣ linearTerm ∣ + ∣ plusTerm ∣) + ∣ minusTerm ∣
    triangle = ℚP.≤-trans firstTriangle secondTriangle

    productsMeaning :
      (∣ linearTerm ∣ + ∣ plusTerm ∣) + ∣ minusTerm ∣
      ≡ innerAbsoluteEnvelope sample
    productsMeaning
      rewrite ℚP.∣p*q∣≡∣p∣*∣q∣
        (Second.linearIncrement sample)
        (Second.plusDerivative sample - Second.minusDerivative sample)
            | ℚP.∣p*q∣≡∣p∣*∣q∣
        (Second.plusRemainder sample) (Second.plusDerivative sample)
            | ℚP.∣p*q∣≡∣p∣*∣q∣
        (Second.minusRemainder sample) (Second.minusDerivative sample) = refl
  in
  subst
    (λ upper → ∣ innerSigned sample ∣ ≤ upper)
    productsMeaning triangle

signedSecondOrderDefectBelowAbsoluteMagnitude :
  (displacement : ℚ) →
  (displacementNN : 0ℚ ≤ displacement) →
  (sample : Second.PairedCommutatorSample) →
  Second.pairedSecondOrderDefect sample
  ≤ Moment.pairedMagnitude
      (absoluteMagnitudeSample displacement displacementNN sample)
signedSecondOrderDefectBelowAbsoluteMagnitude displacement displacementNN sample =
  let
    defect = Second.pairedSecondOrderDefect sample
    weightAbs = ∣ Second.weight sample ∣

    defectBelowAbsolute : defect ≤ ∣ defect ∣
    defectBelowAbsolute = ℚP.p≤∣p∣ defect

    absoluteDefectMeaning :
      ∣ defect ∣
      ≡ weightAbs * ∣ innerSigned sample ∣
    absoluteDefectMeaning =
      ℚP.∣p*q∣≡∣p∣*∣q∣
        (Second.weight sample) (innerSigned sample)

    defectBelowWeightedAbsoluteInner :
      defect ≤ weightAbs * ∣ innerSigned sample ∣
    defectBelowWeightedAbsoluteInner =
      subst (λ upper → defect ≤ upper)
        absoluteDefectMeaning defectBelowAbsolute

    weightedEnvelope :
      weightAbs * ∣ innerSigned sample ∣
      ≤ weightAbs * innerAbsoluteEnvelope sample
    weightedEnvelope =
      let
        instance weightNN = nonNegative (ℚP.0≤∣p∣ (Second.weight sample))
      in
      ℚP.*-monoˡ-≤-nonNeg weightAbs
        (innerSignedAbsoluteBelowEnvelope sample)
  in
  ℚP.≤-trans defectBelowWeightedAbsoluteInner weightedEnvelope

roundAbsoluteMagnitudeCarrierClosed : Bool
roundAbsoluteMagnitudeCarrierClosed = true

roundSignedDefectToMagnitudeClosed : Bool
roundSignedDefectToMagnitudeClosed = true

roundIntroducesPhysicalEnvelopeEstimate : Bool
roundIntroducesPhysicalEnvelopeEstimate = false
