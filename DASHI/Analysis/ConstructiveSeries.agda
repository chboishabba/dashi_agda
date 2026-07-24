module DASHI.Analysis.ConstructiveSeries where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Nat.Base using (_∸_)

open import DASHI.Analysis.ConstructiveRealSpine

------------------------------------------------------------------------
-- Executable finite algebra.

powerR :
  (R : ConstructedOrderedCompleteReal) →
  Real R → Nat → Real R
powerR R x zero = one R
powerR R x (suc n) = _*_ R x (powerR R x n)

finiteSumThrough :
  (R : ConstructedOrderedCompleteReal) →
  (Nat → Real R) → Nat → Real R
finiteSumThrough R term zero = term zero
finiteSumThrough R term (suc n) =
  _+_ R (finiteSumThrough R term n) (term (suc n))

partialSumFunction :
  (R : ConstructedOrderedCompleteReal) →
  (Nat → Real R) → Nat → Real R
partialSumFunction = finiteSumThrough

convolutionCoefficient :
  (R : ConstructedOrderedCompleteReal) →
  (Nat → Real R) →
  (Nat → Real R) →
  Nat → Real R
convolutionCoefficient R left right k =
  finiteSumThrough R
    (λ m → _*_ R (left m) (right (k ∸ m)))
    k

------------------------------------------------------------------------
-- The abstract constructed-real record intentionally does not assume that every
-- Agda function Nat → Real is already one of its admitted sequences.  This
-- small realization interface makes that bridge explicit.

record FunctionSequenceRealization
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    fromFunction : (Nat → Real R) → Sequence R
    sequenceAtFromFunction : ∀ f n →
      sequenceAt R (fromFunction f) n ≡ f n

open FunctionSequenceRealization public

seriesPartialSums :
  ∀ {R : ConstructedOrderedCompleteReal} →
  FunctionSequenceRealization R →
  (Nat → Real R) →
  Sequence R
seriesPartialSums S term =
  fromFunction S (partialSumFunction _ term)

------------------------------------------------------------------------
-- Convergence and domination packages.

record ConvergentSeries
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R)
  (term : Nat → Real R) : Set₁ where
  field
    partialSumsCauchy : IsCauchy R (seriesPartialSums S term)
    limit : Real R
    converges : ConvergesTo R (seriesPartialSums S term) limit

open ConvergentSeries public

asConstructedSeries :
  ∀ {R : ConstructedOrderedCompleteReal}
    {S : FunctionSequenceRealization R}
    {term : Nat → Real R} →
  ConvergentSeries R S term →
  ConstructedSeries R
asConstructedSeries {R} {S} {term} C =
  record
    { term = term
    ; partialSums = seriesPartialSums S term
    ; partialSumsMatch = λ _ → refl
    ; cauchy = partialSumsCauchy C
    ; sum = limit C
    ; sumsTo = converges C
    }

record AbsoluteConvergence
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R)
  (term : Nat → Real R) : Set₁ where
  field
    absoluteTerms : Nat → Real R
    absoluteTermsAreAbs : ∀ n → absoluteTerms n ≡ abs R (term n)
    absoluteSeriesConverges : ConvergentSeries R S absoluteTerms

open AbsoluteConvergence public

record TailBound
  (R : ConstructedOrderedCompleteReal)
  (term : Nat → Real R) : Set₁ where
  field
    tailMajorant : Nat → Real R
    tailMajorantNonnegative : ∀ n → _≤_ R (zero R) (tailMajorant n)
    tailTendsToZero : Set
    everyFiniteTailControlled : ∀ start finish → Set

open TailBound public

record GeometricSeriesAuthority
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R) : Set₁ where
  field
    ratio : Real R
    RatioAdmissible : Set
    geometricTerm : Nat → Real R
    geometricTermDefinition : ∀ n → geometricTerm n ≡ powerR R ratio n
    geometricConverges : ConvergentSeries R S geometricTerm
    geometricTail : TailBound R geometricTerm

open GeometricSeriesAuthority public

record ComparisonTestAuthority
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R) : Set₁ where
  field
    comparisonTest :
      ∀ {term majorant} →
      (∀ n → _≤_ R (abs R (term n)) (majorant n)) →
      ConvergentSeries R S majorant →
      AbsoluteConvergence R S term

open ComparisonTestAuthority public

record RatioTailCertificate
  (R : ConstructedOrderedCompleteReal)
  (term : Nat → Real R) : Set₁ where
  field
    cutoff : Nat
    ratioBound : Real R
    ratioBoundAdmissible : Set
    successiveTermControlled : ∀ n → Set

open RatioTailCertificate public

record RatioTestAuthority
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R) : Set₁ where
  field
    ratioTest : ∀ {term} →
      RatioTailCertificate R term →
      AbsoluteConvergence R S term

open RatioTestAuthority public

------------------------------------------------------------------------
-- Cauchy products and finite binomial algebra.

record CauchyProductAuthority
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R) : Set₁ where
  field
    productConverges :
      ∀ {left right} →
      AbsoluteConvergence R S left →
      AbsoluteConvergence R S right →
      ConvergentSeries R S (convolutionCoefficient R left right)

    productLimitIsProduct :
      ∀ {left right}
        (leftAbs : AbsoluteConvergence R S left)
        (rightAbs : AbsoluteConvergence R S right) →
      limit (productConverges leftAbs rightAbs)
      ≡ _*_ R
          (limit (absoluteSeriesConverges leftAbs))
          (limit (absoluteSeriesConverges rightAbs))

open CauchyProductAuthority public

record NaturalEmbedding
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    nat : Nat → Real R
    natZero : nat zero ≡ zero R
    natSuc : ∀ n → nat (suc n) ≡ _+_ R (nat n) (one R)

open NaturalEmbedding public

record FactorialAuthority
  (R : ConstructedOrderedCompleteReal)
  (N : NaturalEmbedding R) : Set₁ where
  field
    factorialNat : Nat → Nat
    factorialNatZero : factorialNat zero ≡ suc zero
    factorialNatSuc : ∀ n → factorialNat (suc n) ≡ suc n *N factorialNat n
    factorial : Nat → Real R
    factorialEmbedded : ∀ n → factorial n ≡ nat N (factorialNat n)
    reciprocal : Real R → Real R
    factorialNonzero : ∀ n → Set

  _*N_ : Nat → Nat → Nat
  zero *N n = zero
  suc m *N n = n +N (m *N n)
    where
      _+N_ : Nat → Nat → Nat
      zero +N k = k
      suc j +N k = suc (j +N k)

open FactorialAuthority public

record BinomialAuthority
  (R : ConstructedOrderedCompleteReal)
  (N : NaturalEmbedding R) : Set₁ where
  field
    choose : Nat → Nat → Nat
    chooseAsReal : Nat → Nat → Real R
    chooseEmbedded : ∀ n k → chooseAsReal n k ≡ nat N (choose n k)

    binomialTheorem : ∀ x y n →
      finiteSumThrough R
        (λ k →
          _*_ R
            (chooseAsReal n k)
            (_*_ R
              (powerR R x k)
              (powerR R y (n ∸ k))))
        n
      ≡ powerR R (_+_ R x y) n

open BinomialAuthority public

------------------------------------------------------------------------
-- Exact series theorem cutsets consumed by exp, sin and cos realizations.

record ExponentialSeriesCutset
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R)
  (N : NaturalEmbedding R) : Set₁ where
  field
    factorialAuthority : FactorialAuthority R N
    expTerm : Real R → Nat → Real R
    expTermDefinition : ∀ x n →
      expTerm x n
      ≡ _*_ R
          (powerR R x n)
          (reciprocal factorialAuthority (factorial factorialAuthority n))

    expAbsoluteConvergence : ∀ x → AbsoluteConvergence R S (expTerm x)
    cauchyProductAuthority : CauchyProductAuthority R S
    binomialAuthority : BinomialAuthority R N

open ExponentialSeriesCutset public

record TrigonometricSeriesCutset
  (R : ConstructedOrderedCompleteReal)
  (S : FunctionSequenceRealization R) : Set₁ where
  field
    sineTerm cosineTerm : Real R → Nat → Real R
    sineAbsoluteConvergence : ∀ x → AbsoluteConvergence R S (sineTerm x)
    cosineAbsoluteConvergence : ∀ x → AbsoluteConvergence R S (cosineTerm x)
    additionFormulaAuthority : Set
    pythagoreanAuthority : Set
    firstPositiveZeroAuthority : Set

open TrigonometricSeriesCutset public
