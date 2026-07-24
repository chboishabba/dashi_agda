module DASHI.Analysis.OrdinaryTranscendentalRealization where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex

------------------------------------------------------------------------
-- Exact theorem-producing bridge from ordinary series analysis into the EML
-- transcendental records.  Nothing here assumes convergence merely from a
-- syntax tree: every series, product, monotonicity, and inverse theorem is an
-- explicit input and is preserved in the resulting package.

record ExponentialPowerSeriesAuthority
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    factorial : Nat → Real R
    power : Real R → Nat → Real R

    exponentialSeries : Real R → ConstructedSeries R
    exp : Real R → Real R
    expIsSeriesSum : ∀ x → exp x ≡ sum (exponentialSeries x)

    expZero : exp (zero R) ≡ one R
    expAdd : ∀ x y → exp (_+_ R x y) ≡ _*_ R (exp x) (exp y)

    Positive : Real R → Set
    onePositive : Positive (one R)
    expPositive : ∀ x → Positive (exp x)
    expInjective : ∀ {x y} → exp x ≡ exp y → x ≡ y
    expStrictMonotone : ∀ {x y} → _<_ R x y → _<_ R (exp x) (exp y)
    expOntoPositive : ∀ y → Positive y → Σ (Real R) (λ x → exp x ≡ y)

open ExponentialPowerSeriesAuthority public

powerSeriesExponential :
  ∀ {R : ConstructedOrderedCompleteReal} →
  ExponentialPowerSeriesAuthority R →
  ConstructedRealExponential R
powerSeriesExponential A =
  record
    { factorial = factorial A
    ; power = power A
    ; exponentialSeries = exponentialSeries A
    ; exp = exp A
    ; expIsSeriesSum = expIsSeriesSum A
    ; expZero = expZero A
    ; expAdd = expAdd A
    ; Positive = Positive A
    ; onePositive = onePositive A
    ; expPositive = expPositive A
    ; expInjective = expInjective A
    ; expStrictMonotone = expStrictMonotone A
    ; expOntoPositive = expOntoPositive A
    }

record PositiveExponentialInverseAuthority
  (R : ConstructedOrderedCompleteReal)
  (E : ConstructedRealExponential R) : Set₁ where
  field
    log : (y : Real R) → Positive E y → Real R
    expLog : ∀ y py → exp E (log y py) ≡ y
    logExp : ∀ x → log (exp E x) (expPositive E x) ≡ x
    logOne : log (one R) (onePositive E) ≡ zero R
    positiveMul : ∀ {x y} → Positive E x → Positive E y → Positive E (_*_ R x y)
    logMul : ∀ x y px py →
      log (_*_ R x y) (positiveMul px py)
      ≡ _+_ R (log x px) (log y py)

open PositiveExponentialInverseAuthority public

positiveInverseLogarithm :
  ∀ {R : ConstructedOrderedCompleteReal}
    {E : ConstructedRealExponential R} →
  PositiveExponentialInverseAuthority R E →
  ConstructedRealLogarithm R E
positiveInverseLogarithm A =
  record
    { log = log A
    ; expLog = expLog A
    ; logExp = logExp A
    ; logOne = logOne A
    ; positiveMul = positiveMul A
    ; logMul = logMul A
    }

record TrigonometricPowerSeriesAuthority
  (R : ConstructedOrderedCompleteReal)
  (E : ConstructedRealExponential R) : Set₁ where
  field
    sineSeries cosineSeries : Real R → ConstructedSeries R
    sin cos : Real R → Real R
    sinIsSeriesSum : ∀ x → sin x ≡ sum (sineSeries x)
    cosIsSeriesSum : ∀ x → cos x ≡ sum (cosineSeries x)

    pi : Real R

    sinZero : sin (zero R) ≡ zero R
    cosZero : cos (zero R) ≡ one R
    sinNeg : ∀ x → sin (neg R x) ≡ neg R (sin x)
    cosNeg : ∀ x → cos (neg R x) ≡ cos x
    sinAdd : ∀ x y →
      sin (_+_ R x y)
      ≡ _+_ R (_*_ R (sin x) (cos y)) (_*_ R (cos x) (sin y))
    cosAdd : ∀ x y →
      cos (_+_ R x y)
      ≡ _-_ R (_*_ R (cos x) (cos y)) (_*_ R (sin x) (sin y))
    pythagorean : ∀ x →
      _+_ R (_*_ R (sin x) (sin x)) (_*_ R (cos x) (cos x)) ≡ one R

    sinPi : sin pi ≡ zero R
    cosPi : cos pi ≡ neg R (one R)

    expC : ComplexPair R → ComplexPair R
    expCartesian : ∀ x y →
      expC (complex x y)
      ≡ complex
          (_*_ R (exp E x) (cos y))
          (_*_ R (exp E x) (sin y))

open TrigonometricPowerSeriesAuthority public

constructedComplexExponentialFromSeries :
  ∀ {R : ConstructedOrderedCompleteReal}
    {E : ConstructedRealExponential R} →
  TrigonometricPowerSeriesAuthority R E →
  ConstructedComplexExponential R E
constructedComplexExponentialFromSeries A =
  record
    { sin = sin A
    ; cos = cos A
    ; pi = pi A
    ; expC = expC A
    ; expCartesian = expCartesian A
    }

ordinaryTranscendentalPackage :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (EA : ExponentialPowerSeriesAuthority R) →
  PositiveExponentialInverseAuthority R (powerSeriesExponential EA) →
  ConstructedRealTranscendentalPackage
ordinaryTranscendentalPackage {R} EA LA =
  record
    { real = R
    ; exponential = powerSeriesExponential EA
    ; logarithm = positiveInverseLogarithm LA
    }
