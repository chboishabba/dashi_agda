module DASHI.Physics.Closure.NSTriadKNCenteredResolventKernelEnvelopeExact where

------------------------------------------------------------------------
-- CENTERED RESOLVENT KERNEL: TWO COMPLEMENTARY EXACT ENVELOPES
--
-- For a > 0 and s >= 0, define
--
--        K(a,s) = s / (a (a+s))
--               = s * (a+s)^(-1) * a^(-1).
--
-- This is exactly the scalar coefficient multiplying the R290 Gram scalar in
-- the fixed-output centered-resolvent correction.
--
-- Two bounds are simultaneously useful:
--
--   K(a,s) <= s / a^2      (small/centered defect branch)
--   K(a,s) <= 1 / a        (large-defect saturation branch)
--
-- The first retains the centered-frequency gain needed by the Taylor/second-
-- moment lane.  The second shows the resolvent defect saturates instead of
-- growing linearly in s.  Both are proved over exact rationals from positive
-- reciprocal antitonicity; there is no shell count or PDE estimate here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

invPositive : (x : ℚ) → 0ℚ < x → ℚ
invPositive = Quotient.positiveReciprocal

centeredResolventKernel :
  (a s : ℚ) →
  (aPositive : 0ℚ < a) →
  (aPlusSPositive : 0ℚ < a + s) →
  ℚ
centeredResolventKernel a s aPositive aPlusSPositive =
  s * invPositive (a + s) aPlusSPositive * invPositive a aPositive

smallDefectEnvelope :
  (a s : ℚ) → (aPositive : 0ℚ < a) → ℚ
smallDefectEnvelope a s aPositive =
  s * invPositive a aPositive * invPositive a aPositive

saturationEnvelope :
  (a : ℚ) → (aPositive : 0ℚ < a) → ℚ
saturationEnvelope a aPositive =
  invPositive a aPositive

positivePlusNonnegative :
  ∀ {a s : ℚ} →
  0ℚ < a → 0ℚ ≤ s → 0ℚ < a + s
positivePlusNonnegative {a} {s} aPositive sNN =
  ℚP.<-≤-trans
    (subst (0ℚ <_) (sym (ℚP.+-identityʳ a)) aPositive)
    (ℚP.+-monoˡ-≤ a sNN)

baseBelowBasePlusDefect :
  ∀ {a s : ℚ} → 0ℚ ≤ s → a ≤ a + s
baseBelowBasePlusDefect {a} {s} sNN =
  subst (a ≤_) (sym (ℚP.+-identityʳ a))
    (ℚP.+-monoˡ-≤ a sNN)

kernelNonnegative :
  (a s : ℚ) →
  (aPositive : 0ℚ < a) →
  (sNN : 0ℚ ≤ s) →
  0ℚ ≤ centeredResolventKernel a s aPositive
    (positivePlusNonnegative aPositive sNN)
kernelNonnegative a s aPositive sNN =
  let
    ap = a + s
    apPositive = positivePlusNonnegative aPositive sNN
    ia = invPositive a aPositive
    iap = invPositive ap apPositive

    iaNN : 0ℚ ≤ ia
    iaNN = ℚP.<⇒≤ (Quotient.positiveReciprocalPositive a aPositive)

    iapNN : 0ℚ ≤ iap
    iapNN = ℚP.<⇒≤ (Quotient.positiveReciprocalPositive ap apPositive)

    instance
      sNNI : NonNegative s
      sNNI = nonNegative sNN
      iapNNI : NonNegative iap
      iapNNI = nonNegative iapNN
      firstNNI = ℚP.nonNeg*nonNeg⇒nonNeg s iap
      iaNNI : NonNegative ia
      iaNNI = nonNegative iaNN
      totalNNI = ℚP.nonNeg*nonNeg⇒nonNeg (s * iap) ia
  in
  ℚP.nonNegative⁻¹ ((s * iap) * ia)

kernelBelowSmallDefectEnvelope :
  (a s : ℚ) →
  (aPositive : 0ℚ < a) →
  (sNN : 0ℚ ≤ s) →
  centeredResolventKernel a s aPositive
      (positivePlusNonnegative aPositive sNN)
  ≤ smallDefectEnvelope a s aPositive
kernelBelowSmallDefectEnvelope a s aPositive sNN =
  let
    ap = a + s
    apPositive = positivePlusNonnegative aPositive sNN
    ia = invPositive a aPositive
    iap = invPositive ap apPositive

    aBelowAp : a ≤ ap
    aBelowAp = baseBelowBasePlusDefect sNN

    iapBelowIa : iap ≤ ia
    iapBelowIa =
      Quotient.reciprocalAntitonePositive
        a ap aPositive apPositive aBelowAp

    iaNN : 0ℚ ≤ ia
    iaNN = ℚP.<⇒≤ (Quotient.positiveReciprocalPositive a aPositive)

    instance
      sNNI : NonNegative s
      sNNI = nonNegative sNN
      iaNNI : NonNegative ia
      iaNNI = nonNegative iaNN

    first :
      s * iap ≤ s * ia
    first = ℚP.*-monoˡ-≤-nonNeg s iapBelowIa

    second :
      (s * iap) * ia ≤ (s * ia) * ia
    second = ℚP.*-monoʳ-≤-nonNeg ia first
  in
  second

defectFractionBelowOne :
  (a s : ℚ) →
  (aPositive : 0ℚ < a) →
  (sNN : 0ℚ ≤ s) →
  s * invPositive (a + s) (positivePlusNonnegative aPositive sNN)
  ≤ 1ℚ
defectFractionBelowOne a s aPositive sNN =
  let
    ap = a + s
    apPositive = positivePlusNonnegative aPositive sNN
    iap = invPositive ap apPositive

    sBelowAp : s ≤ ap
    sBelowAp =
      subst (s ≤_) (sym (ℚP.+-identityˡ s))
        (ℚP.+-monoʳ-≤ s (ℚP.<⇒≤ aPositive))

    iapNN : 0ℚ ≤ iap
    iapNN = ℚP.<⇒≤ (Quotient.positiveReciprocalPositive ap apPositive)

    instance
      iapNNI : NonNegative iap
      iapNNI = nonNegative iapNN

    scaled : s * iap ≤ ap * iap
    scaled = ℚP.*-monoʳ-≤-nonNeg iap sBelowAp

    collapse : ap * iap ≡ 1ℚ
    collapse = Quotient.positiveReciprocalRightInverse ap apPositive
  in
  subst (s * iap ≤_) collapse scaled

kernelBelowSaturationEnvelope :
  (a s : ℚ) →
  (aPositive : 0ℚ < a) →
  (sNN : 0ℚ ≤ s) →
  centeredResolventKernel a s aPositive
      (positivePlusNonnegative aPositive sNN)
  ≤ saturationEnvelope a aPositive
kernelBelowSaturationEnvelope a s aPositive sNN =
  let
    apPositive = positivePlusNonnegative aPositive sNN
    ia = invPositive a aPositive

    fractionBound :
      s * invPositive (a + s) apPositive ≤ 1ℚ
    fractionBound = defectFractionBelowOne a s aPositive sNN

    iaNN : 0ℚ ≤ ia
    iaNN = ℚP.<⇒≤ (Quotient.positiveReciprocalPositive a aPositive)

    instance
      iaNNI : NonNegative ia
      iaNNI = nonNegative iaNN

    scaled :
      (s * invPositive (a + s) apPositive) * ia
      ≤ 1ℚ * ia
    scaled = ℚP.*-monoʳ-≤-nonNeg ia fractionBound
  in
  subst
    ((s * invPositive (a + s) apPositive) * ia ≤_)
    (ℚP.*-identityˡ ia)
    scaled

centeredResolventKernelTwoEnvelopeAnalyticLemmaClosed : Bool
centeredResolventKernelTwoEnvelopeAnalyticLemmaClosed = true

smallDefectEnvelopeRetainsCenteredMultiplier : Bool
smallDefectEnvelopeRetainsCenteredMultiplier = true

saturationEnvelopeIndependentOfCenteredDefect : Bool
saturationEnvelopeIndependentOfCenteredDefect = true

cutoffUniformPhysicalSumClosedHere : Bool
cutoffUniformPhysicalSumClosedHere = false

clayPromotion : Bool
clayPromotion = false

centeredResolventKernelTwoEnvelopeAnalyticLemmaClosedIsTrue :
  centeredResolventKernelTwoEnvelopeAnalyticLemmaClosed ≡ true
centeredResolventKernelTwoEnvelopeAnalyticLemmaClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
