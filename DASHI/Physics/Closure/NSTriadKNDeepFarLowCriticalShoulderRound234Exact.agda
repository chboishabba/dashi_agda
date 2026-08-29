module DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact where

------------------------------------------------------------------------
-- ROUND234 / DEEP FAR-LOW ENERGY PAYMENT THRESHOLD
--
-- Round227 identifies the authoritative A-facing companion with the bare
-- mixed-helicity convolution mass
--
--   Q_+- = sum_k | sum_{p+q=k} u_p+ x u_q- |^2.
--
-- Round232 shows that this bare +/- symbol has no generic pointwise FL scale
-- gain.  Therefore the historical pure-commutator identity of Round120 must
-- not be silently imported as an automatic estimate for the Round227 object.
--
-- There is nevertheless a genuinely routine deep-FL region.  For dyadic
-- shells l <= m, the standard low-in-L-infinity estimate has squared spatial
-- coefficient
--
--   2^(3 l).
--
-- Paying the high factor with the Leray H1 budget supplies
--
--   2^(2 m).
--
-- Hence energy+dissipation can absorb the interaction whenever
--
--   3 l <= 2 m.                                             (DFL)
--
-- The old fixed-gap Bony far-low condition l <= m-C is much larger.  Its
-- residual shoulder
--
--   2 m < 3 l <= 3(m-C)
--
-- is still critical and must travel with the comparable-scale rigidity
-- problem.  Thus the correct post-Round232 split is
--
--   deep FL                  : 3 l <= 2 m       (routine E*D payment)
--   critical FL shoulder     : 2 m < 3 l        (not energy-payable)
--   HH -> low                : opposite-helicity null geometry
--   remaining critical core  : shoulder + comparable interactions.
--
-- This module deliberately formalises the exponent decision and the generic
-- monotone scalar payment compiler.  It does NOT claim that the repository
-- already contains a kernel-backed Bernstein theorem identifying every
-- physical deep-FL shell with the scalar hypotheses below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)

one two three : ℚ
one = 1ℚ
two = one + one
three = two + one

bernsteinSquaredExponent : ℚ → ℚ
bernsteinSquaredExponent lowShell = three * lowShell

lerayHighSquaredExponent : ℚ → ℚ
lerayHighSquaredExponent highShell = two * highShell

deepFarLowExponentCondition : ℚ → ℚ → Set
deepFarLowExponentCondition lowShell highShell =
  bernsteinSquaredExponent lowShell ≤ lerayHighSquaredExponent highShell

criticalShoulderExcess : ℚ → ℚ → ℚ
criticalShoulderExcess lowShell highShell =
  bernsteinSquaredExponent lowShell - lerayHighSquaredExponent highShell

criticalThresholdAtTwoThirds : (m : ℚ) →
  bernsteinSquaredExponent (two * m)
  ≡ lerayHighSquaredExponent (three * m)
criticalThresholdAtTwoThirds m = solve (m ∷ [])

-- Scalar compiler for a single dyadic pair.  The analytic producer may use
-- any concrete nonnegative Bernstein and derivative coefficients; once the
-- former is below the latter, the shell product is paid by low energy times
-- high dissipation without a fibre-count or Wiener-l1 factor.
record DeepFarLowScalarPayment : Set where
  constructor deep-far-low-scalar-payment
  field
    lowEnergy highEnergy : ℚ
    bernsteinCoefficient highDerivativeCoefficient : ℚ
    productMass : ℚ

    lowEnergyNN : 0ℚ ≤ lowEnergy
    highEnergyNN : 0ℚ ≤ highEnergy
    bernsteinCoefficientNN : 0ℚ ≤ bernsteinCoefficient
    highDerivativeCoefficientNN : 0ℚ ≤ highDerivativeCoefficient

    coefficientPayment :
      bernsteinCoefficient ≤ highDerivativeCoefficient

    productMassBound :
      productMass
      ≤ bernsteinCoefficient * lowEnergy * highEnergy

open DeepFarLowScalarPayment public

highDissipation : DeepFarLowScalarPayment → ℚ
highDissipation P = highDerivativeCoefficient P * highEnergy P

coefficientTimesEnergyMonotone :
  (P : DeepFarLowScalarPayment) →
  bernsteinCoefficient P * lowEnergy P * highEnergy P
  ≤ lowEnergy P * highDissipation P
coefficientTimesEnergyMonotone P =
  let
    b = bernsteinCoefficient P
    h = highDerivativeCoefficient P
    eL = lowEnergy P
    eH = highEnergy P

    instance
      bNN = Data.Rational.Base.nonNegative (bernsteinCoefficientNN P)
      hNN = Data.Rational.Base.nonNegative (highDerivativeCoefficientNN P)
      eLNN = Data.Rational.Base.nonNegative (lowEnergyNN P)
      eHNN = Data.Rational.Base.nonNegative (highEnergyNN P)

    step1 : b * eL ≤ h * eL
    step1 = ℚP.*-monoʳ-≤-nonNeg eL (coefficientPayment P)

    step2 : (b * eL) * eH ≤ (h * eL) * eH
    step2 = ℚP.*-monoʳ-≤-nonNeg eH step1

    rearrangeLeft : (b * eL) * eH ≡ b * eL * eH
    rearrangeLeft = refl

    rearrangeRight : (h * eL) * eH ≡ eL * (h * eH)
    rearrangeRight = solve (b ∷ h ∷ eL ∷ eH ∷ [])
  in
  subst₂ rearrangeLeft rearrangeRight step2
  where
  subst₂ : ∀ {a b c d : ℚ} → a ≡ b → c ≡ d → a ≤ c → b ≤ d
  subst₂ refl refl p = p

deepFarLowMassPaidByEnergyTimesDissipation :
  (P : DeepFarLowScalarPayment) →
  productMass P ≤ lowEnergy P * highDissipation P
deepFarLowMassPaidByEnergyTimesDissipation P =
  ℚP.≤-trans
    (productMassBound P)
    (coefficientTimesEnergyMonotone P)

round234DeepFarLowExponentThresholdIdentified : Bool
round234DeepFarLowExponentThresholdIdentified = true

round234DeepFarLowScalarPaymentCompilerClosed : Bool
round234DeepFarLowScalarPaymentCompilerClosed = true

round234PhysicalBernsteinShellWeldClosed : Bool
round234PhysicalBernsteinShellWeldClosed = false

round234EntireFixedGapFarLowRegionEnergyPayable : Bool
round234EntireFixedGapFarLowRegionEnergyPayable = false

round234CriticalFarLowShoulderRemains : Bool
round234CriticalFarLowShoulderRemains = true

round234CriticalCoreIsOnlyConstantWidthComparable : Bool
round234CriticalCoreIsOnlyConstantWidthComparable = false

round234PackageAClosed : Bool
round234PackageAClosed = false

round234ClayPromotion : Bool
round234ClayPromotion = false

round234DeepFarLowExponentThresholdIdentifiedIsTrue :
  round234DeepFarLowExponentThresholdIdentified ≡ true
round234DeepFarLowExponentThresholdIdentifiedIsTrue = refl

round234DeepFarLowScalarPaymentCompilerClosedIsTrue :
  round234DeepFarLowScalarPaymentCompilerClosed ≡ true
round234DeepFarLowScalarPaymentCompilerClosedIsTrue = refl

round234PhysicalBernsteinShellWeldClosedIsFalse :
  round234PhysicalBernsteinShellWeldClosed ≡ false
round234PhysicalBernsteinShellWeldClosedIsFalse = refl

round234EntireFixedGapFarLowRegionEnergyPayableIsFalse :
  round234EntireFixedGapFarLowRegionEnergyPayable ≡ false
round234EntireFixedGapFarLowRegionEnergyPayableIsFalse = refl

round234CriticalFarLowShoulderRemainsIsTrue :
  round234CriticalFarLowShoulderRemains ≡ true
round234CriticalFarLowShoulderRemainsIsTrue = refl

round234PackageAClosedIsFalse : round234PackageAClosed ≡ false
round234PackageAClosedIsFalse = refl

round234ClayPromotionIsFalse : round234ClayPromotion ≡ false
round234ClayPromotionIsFalse = refl
