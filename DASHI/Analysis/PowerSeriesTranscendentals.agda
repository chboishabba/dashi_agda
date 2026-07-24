module DASHI.Analysis.PowerSeriesTranscendentals where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConstructiveSeries
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Analysis.OrdinaryTranscendentalRealization

------------------------------------------------------------------------
-- Uniqueness of limits turns coefficient identities into function identities.

record SeriesExtensionalityAuthority
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R) : Set₁ where
  field
    equalTermsHaveEqualLimits :
      ∀ {left right}
        (leftConverges : ConvergentSeries R S left)
        (rightConverges : ConvergentSeries R S right) →
      (∀ n → left n ≡ right n) →
      limit leftConverges ≡ limit rightConverges

open SeriesExtensionalityAuthority public

seriesExponentialValue :
  ∀ {R : ConstructedOrderedCompleteReal}
    {S : FunctionSequenceRealization R}
    {N : NaturalEmbedding R} →
  ExponentialSeriesCutset R S N →
  Real R →
  Real R
seriesExponentialValue C x =
  limit (seriesConverges (expAbsoluteConvergence C x))

seriesExponential :
  ∀ {R : ConstructedOrderedCompleteReal}
    {S : FunctionSequenceRealization R}
    {N : NaturalEmbedding R} →
  ExponentialSeriesCutset R S N →
  Real R →
  ConstructedSeries R
seriesExponential C x =
  asConstructedSeries (seriesConverges (expAbsoluteConvergence C x))

record ExponentialCoefficientIdentity
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R)
  (N : NaturalEmbedding R)
  (C : ExponentialSeriesCutset R S N) : Set₁ where
  field
    convolutionIsExpOfSum : ∀ x y n →
      convolutionCoefficient R (expTerm C x) (expTerm C y) n
      ≡ expTerm C (_+_ R x y) n

open ExponentialCoefficientIdentity public

record ExponentialOrderLaws
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R)
  (N : NaturalEmbedding R)
  (C : ExponentialSeriesCutset R S N) : Set₁ where

  expValue : Real R → Real R
  expValue = seriesExponentialValue C

  field
    expZero : expValue (zero R) ≡ one R

    Positive : Real R → Set
    onePositive : Positive (one R)
    expPositive : ∀ x → Positive (expValue x)
    expInjective : ∀ {x y} → expValue x ≡ expValue y → x ≡ y
    expStrictMonotone : ∀ {x y} →
      _<_ R x y → _<_ R (expValue x) (expValue y)
    expOntoPositive : ∀ y →
      Positive y →
      Agda.Builtin.Sigma.Σ (Real R) (λ x → expValue x ≡ y)

open ExponentialOrderLaws public

expAddFromCauchyProduct :
  ∀ {R : ConstructedOrderedCompleteReal}
    {S : FunctionSequenceRealization R}
    {N : NaturalEmbedding R}
    (C : ExponentialSeriesCutset R S N) →
  SeriesExtensionalityAuthority R S →
  ExponentialCoefficientIdentity R S N C →
  ∀ x y →
  seriesExponentialValue C (_+_ R x y)
  ≡ _*_ R (seriesExponentialValue C x) (seriesExponentialValue C y)
expAddFromCauchyProduct {R} C limits coefficients x y =
  trans (sym productEqualsSumSeries) productEqualsProduct
  where
    leftAbs : AbsoluteConvergence R _ (expTerm C x)
    leftAbs = expAbsoluteConvergence C x

    rightAbs : AbsoluteConvergence R _ (expTerm C y)
    rightAbs = expAbsoluteConvergence C y

    productSeries :
      ConvergentSeries R _
        (convolutionCoefficient R (expTerm C x) (expTerm C y))
    productSeries =
      productConverges (cauchyProductAuthority C) leftAbs rightAbs

    sumSeries :
      ConvergentSeries R _ (expTerm C (_+_ R x y))
    sumSeries =
      seriesConverges (expAbsoluteConvergence C (_+_ R x y))

    productEqualsSumSeries :
      limit productSeries ≡ limit sumSeries
    productEqualsSumSeries =
      equalTermsHaveEqualLimits limits
        productSeries
        sumSeries
        (convolutionIsExpOfSum coefficients x y)

    productEqualsProduct :
      limit productSeries
      ≡ _*_ R (seriesExponentialValue C x) (seriesExponentialValue C y)
    productEqualsProduct =
      productLimitIsProduct
        (cauchyProductAuthority C)
        leftAbs
        rightAbs

exponentialAuthorityFromSeries :
  ∀ {R : ConstructedOrderedCompleteReal}
    {S : FunctionSequenceRealization R}
    {N : NaturalEmbedding R}
    (C : ExponentialSeriesCutset R S N) →
  SeriesExtensionalityAuthority R S →
  ExponentialCoefficientIdentity R S N C →
  ExponentialOrderLaws R S N C →
  ExponentialPowerSeriesAuthority R
exponentialAuthorityFromSeries {R} C limits coefficients order =
  record
    { factorial = factorial (factorialAuthority C)
    ; power = powerR R
    ; exponentialSeries = seriesExponential C
    ; exp = seriesExponentialValue C
    ; expIsSeriesSum = λ _ → refl
    ; expZero = expZero order
    ; expAdd = expAddFromCauchyProduct C limits coefficients
    ; Positive = Positive order
    ; onePositive = onePositive order
    ; expPositive = expPositive order
    ; expInjective = expInjective order
    ; expStrictMonotone = expStrictMonotone order
    ; expOntoPositive = expOntoPositive order
    }

------------------------------------------------------------------------
-- Sine, cosine, and pi are also tied definitionally to their series limits.

seriesSineValue :
  ∀ {R : ConstructedOrderedCompleteReal}
    {S : FunctionSequenceRealization R} →
  TrigonometricSeriesCutset R S →
  Real R → Real R
seriesSineValue C x =
  limit (seriesConverges (sineAbsoluteConvergence C x))

seriesCosineValue :
  ∀ {R : ConstructedOrderedCompleteReal}
    {S : FunctionSequenceRealization R} →
  TrigonometricSeriesCutset R S →
  Real R → Real R
seriesCosineValue C x =
  limit (seriesConverges (cosineAbsoluteConvergence C x))

record FirstPositiveCosineZero
  (R : ConstructedOrderedCompleteReal)
  (cosine : Real R → Real R) : Set₁ where
  field
    halfPi : Real R
    halfPiPositive : _<_ R (zero R) halfPi
    cosineHalfPiZero : cosine halfPi ≡ zero R
    cosinePositiveBefore : ∀ x →
      _<_ R (zero R) x →
      _<_ R x halfPi →
      _<_ R (zero R) (cosine x)

  pi : Real R
  pi = _+_ R halfPi halfPi

open FirstPositiveCosineZero public

record TrigonometricFunctionalLaws
  (R : ConstructedOrderedCompleteReal)
  (E : ConstructedRealExponential R)
  (S : FunctionSequenceRealization R)
  (C : TrigonometricSeriesCutset R S) : Set₁ where

  sin : Real R → Real R
  sin = seriesSineValue C

  cos : Real R → Real R
  cos = seriesCosineValue C

  field
    firstZero : FirstPositiveCosineZero R cos

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
      _+_ R (_*_ R (sin x) (sin x)) (_*_ R (cos x) (cos x))
      ≡ one R

    sinPi : sin (pi firstZero) ≡ zero R
    cosPi : cos (pi firstZero) ≡ neg R (one R)

    expC : ComplexPair R → ComplexPair R
    expCartesian : ∀ x y →
      expC (complex x y)
      ≡ complex
          (_*_ R (exp E x) (cos y))
          (_*_ R (exp E x) (sin y))

open TrigonometricFunctionalLaws public

trigonometricAuthorityFromSeries :
  ∀ {R : ConstructedOrderedCompleteReal}
    {E : ConstructedRealExponential R}
    {S : FunctionSequenceRealization R}
    (C : TrigonometricSeriesCutset R S) →
  TrigonometricFunctionalLaws R E S C →
  TrigonometricPowerSeriesAuthority R E
trigonometricAuthorityFromSeries C laws =
  record
    { sineSeries = λ x →
        asConstructedSeries
          (seriesConverges (sineAbsoluteConvergence C x))
    ; cosineSeries = λ x →
        asConstructedSeries
          (seriesConverges (cosineAbsoluteConvergence C x))
    ; sin = seriesSineValue C
    ; cos = seriesCosineValue C
    ; sinIsSeriesSum = λ _ → refl
    ; cosIsSeriesSum = λ _ → refl
    ; pi = pi (firstZero laws)
    ; sinZero = sinZero laws
    ; cosZero = cosZero laws
    ; sinNeg = sinNeg laws
    ; cosNeg = cosNeg laws
    ; sinAdd = sinAdd laws
    ; cosAdd = cosAdd laws
    ; pythagorean = pythagorean laws
    ; sinPi = sinPi laws
    ; cosPi = cosPi laws
    ; expC = expC laws
    ; expCartesian = expCartesian laws
    }
