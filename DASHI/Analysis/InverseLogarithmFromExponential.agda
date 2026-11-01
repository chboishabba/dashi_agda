module DASHI.Analysis.InverseLogarithmFromExponential where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)
open import Agda.Builtin.Sigma using (fst; snd)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.OrdinaryTranscendentalRealization

------------------------------------------------------------------------
-- Once the exponential package has proved surjectivity onto its positive
-- carrier, logarithm is not an additional analytic primitive.  It is the
-- witness selected by `expOntoPositive`; injectivity proves both inverse laws
-- and transports multiplication to addition.

record PositiveMultiplicationAuthority
  (R : ConstructedOrderedCompleteReal)
  (E : ConstructedRealExponential R) : Set₁ where
  field
    positiveMul : ∀ {x y} →
      Positive E x →
      Positive E y →
      Positive E (_*_ R x y)

open PositiveMultiplicationAuthority public

logFromExponential :
  ∀ {R : ConstructedOrderedCompleteReal}
    (E : ConstructedRealExponential R) →
  (y : Real R) →
  Positive E y →
  Real R
logFromExponential E y py = fst (expOntoPositive E y py)

expLogFromExponential :
  ∀ {R : ConstructedOrderedCompleteReal}
    (E : ConstructedRealExponential R) →
  ∀ y py →
  exp E (logFromExponential E y py) ≡ y
expLogFromExponential E y py = snd (expOntoPositive E y py)

logExpFromExponential :
  ∀ {R : ConstructedOrderedCompleteReal}
    (E : ConstructedRealExponential R) →
  ∀ x →
  logFromExponential E (exp E x) (expPositive E x) ≡ x
logExpFromExponential E x =
  expInjective E
    (expLogFromExponential E (exp E x) (expPositive E x))

logOneFromExponential :
  ∀ {R : ConstructedOrderedCompleteReal}
    (E : ConstructedRealExponential R) →
  logFromExponential E (one R) (onePositive E) ≡ zero R
logOneFromExponential {R} E =
  expInjective E
    (trans
      (expLogFromExponential E (one R) (onePositive E))
      (sym (expZero E)))

logMulFromExponential :
  ∀ {R : ConstructedOrderedCompleteReal}
    (E : ConstructedRealExponential R) →
  (P : PositiveMultiplicationAuthority R E) →
  ∀ x y px py →
  logFromExponential E (_*_ R x y) (positiveMul P px py)
  ≡ _+_ R
      (logFromExponential E x px)
      (logFromExponential E y py)
logMulFromExponential {R} E P x y px py =
  expInjective E
    (trans leftEvaluation (sym rightEvaluation))
  where
    leftEvaluation :
      exp E (logFromExponential E (_*_ R x y) (positiveMul P px py))
      ≡ _*_ R x y
    leftEvaluation =
      expLogFromExponential E (_*_ R x y) (positiveMul P px py)

    rightEvaluation :
      exp E
        (_+_ R
          (logFromExponential E x px)
          (logFromExponential E y py))
      ≡ _*_ R x y
    rightEvaluation =
      trans
        (expAdd E
          (logFromExponential E x px)
          (logFromExponential E y py))
        (cong₂ (_*_ R)
          (expLogFromExponential E x px)
          (expLogFromExponential E y py))

inverseRealLogarithm :
  ∀ {R : ConstructedOrderedCompleteReal}
    (E : ConstructedRealExponential R) →
  PositiveMultiplicationAuthority R E →
  ConstructedRealLogarithm R E
inverseRealLogarithm {R} E P =
  record
    { log = logFromExponential E
    ; expLog = expLogFromExponential E
    ; logExp = logExpFromExponential E
    ; logOne = logOneFromExponential E
    ; positiveMul = positiveMul P
    ; logMul = logMulFromExponential E P
    }

positiveInverseAuthorityFromExponential :
  ∀ {R : ConstructedOrderedCompleteReal}
    (E : ConstructedRealExponential R) →
  (P : PositiveMultiplicationAuthority R E) →
  PositiveExponentialInverseAuthority R E
positiveInverseAuthorityFromExponential {R} E P =
  record
    { log = logFromExponential E
    ; expLog = expLogFromExponential E
    ; logExp = logExpFromExponential E
    ; logOne = logOneFromExponential E
    ; positiveMul = positiveMul P
    ; logMul = logMulFromExponential E P
    }
