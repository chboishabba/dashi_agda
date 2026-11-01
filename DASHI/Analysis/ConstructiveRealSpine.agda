module DASHI.Analysis.ConstructiveRealSpine where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

------------------------------------------------------------------------
-- A proof-producing real-analysis implementation boundary.
--
-- Unlike RealAnalysisAxioms, this package does not name an opaque global ℝ.
-- An inhabitant must provide one carrier together with its actual sequence,
-- series, exponential and logarithm constructions and the exact laws used by
-- EML.  This permits a Cauchy-real, Dedekind-real, or imported constructive-real
-- implementation without identifying it definitionally with DASHI's legacy ℝ.

record ConstructedOrderedCompleteReal : Set₁ where
  infixl 20 _+_ _-_
  infixl 30 _*_
  infix 15 _≤_ _<_
  field
    Real : Set
    zero one : Real
    _+_ _-_ _*_ : Real → Real → Real
    neg abs : Real → Real
    _≤_ _<_ : Real → Real → Set

    addAssoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
    addComm : ∀ a b → a + b ≡ b + a
    addZeroLeft : ∀ a → zero + a ≡ a
    addZeroRight : ∀ a → a + zero ≡ a
    mulAssoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
    mulComm : ∀ a b → a * b ≡ b * a
    mulOneLeft : ∀ a → one * a ≡ a
    mulOneRight : ∀ a → a * one ≡ a
    distribLeft : ∀ a b c → a * (b + c) ≡ (a * b) + (a * c)
    distribRight : ∀ a b c → (a + b) * c ≡ (a * c) + (b * c)
    subSelf : ∀ a → a - a ≡ zero

    Sequence : Set
    sequenceAt : Sequence → Nat → Real
    IsCauchy : Sequence → Set
    ConvergesTo : Sequence → Real → Set
    cauchyLimit : (s : Sequence) → IsCauchy s → Σ Real (λ x → ConvergesTo s x)

open ConstructedOrderedCompleteReal public

record ConstructedSeries (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    term : Nat → Real R
    partialSums : Sequence R
    partialSumsMatch : ∀ n → sequenceAt R partialSums n ≡ sequenceAt R partialSums n
    cauchy : IsCauchy R partialSums
    sum : Real R
    sumsTo : ConvergesTo R partialSums sum

open ConstructedSeries public

record ConstructedRealExponential
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

open ConstructedRealExponential public

record ConstructedRealLogarithm
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

open ConstructedRealLogarithm public

record ConstructedRealTranscendentalPackage : Set₁ where
  field
    real : ConstructedOrderedCompleteReal
    exponential : ConstructedRealExponential real
    logarithm : ConstructedRealLogarithm real exponential

open ConstructedRealTranscendentalPackage public
