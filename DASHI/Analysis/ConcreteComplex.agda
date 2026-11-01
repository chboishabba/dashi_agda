module DASHI.Analysis.ConcreteComplex where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Analysis.ConstructiveRealSpine

record ComplexPair (R : ConstructedOrderedCompleteReal) : Set where
  constructor complex
  field
    re im : Real R

open ComplexPair public

zeroC : ∀ {R} → ComplexPair R
zeroC {R} = complex (zero R) (zero R)

oneC : ∀ {R} → ComplexPair R
oneC {R} = complex (one R) (zero R)

imaginaryUnit : ∀ {R} → ComplexPair R
imaginaryUnit {R} = complex (zero R) (one R)

_+C_ : ∀ {R} → ComplexPair R → ComplexPair R → ComplexPair R
_+C_ {R} (complex a b) (complex c d) =
  complex (_+_ R a c) (_+_ R b d)

_-C_ : ∀ {R} → ComplexPair R → ComplexPair R → ComplexPair R
_-C_ {R} (complex a b) (complex c d) =
  complex (_-_ R a c) (_-_ R b d)

_*C_ : ∀ {R} → ComplexPair R → ComplexPair R → ComplexPair R
_*C_ {R} (complex a b) (complex c d) =
  complex
    (_-_ R (_*_ R a c) (_*_ R b d))
    (_+_ R (_*_ R a d) (_*_ R b c))

conjugateC : ∀ {R} → ComplexPair R → ComplexPair R
conjugateC {R} (complex a b) = complex a (neg R b)

normSqC : ∀ {R} → ComplexPair R → Real R
normSqC {R} (complex a b) = _+_ R (_*_ R a a) (_*_ R b b)

record ComplexAlgebraLaws (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    negInvolutive : ∀ x → neg R (neg R x) ≡ x
    negZero : neg R (zero R) ≡ zero R
    subZeroRight : ∀ x → _-_ R x (zero R) ≡ x
    zeroSub : ∀ x → _-_ R (zero R) x ≡ neg R x

open ComplexAlgebraLaws public

conjugateInvolutiveC :
  ∀ {R} →
  ComplexAlgebraLaws R →
  (z : ComplexPair R) →
  conjugateC (conjugateC z) ≡ z
conjugateInvolutiveC laws (complex a b)
  rewrite negInvolutive laws b = refl

record ConstructedComplexExponential
  (R : ConstructedOrderedCompleteReal)
  (E : ConstructedRealExponential R) : Set₁ where
  field
    sin cos : Real R → Real R
    pi : Real R
    expC : ComplexPair R → ComplexPair R
    expCartesian : ∀ x y →
      expC (complex x y)
      ≡ complex
          (_*_ R (exp E x) (cos y))
          (_*_ R (exp E x) (sin y))

open ConstructedComplexExponential public

record ConstructedComplexPackage : Set₁ where
  field
    realPackage : ConstructedRealTranscendentalPackage
    algebraLaws : ComplexAlgebraLaws (real realPackage)
    complexExponential :
      ConstructedComplexExponential
        (real realPackage)
        (exponential realPackage)

open ConstructedComplexPackage public
