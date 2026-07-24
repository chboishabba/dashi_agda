module DASHI.Analysis.FastCauchyArithmetic where

open import Agda.Builtin.Equality using (_≡_; subst)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

open import DASHI.Analysis.FastCauchyReals

------------------------------------------------------------------------
-- Exact rational leaves needed to lift additive arithmetic to canonical fast
-- representatives.  Addition samples both inputs one precision step deeper:
-- each child then contributes ε(n+1), and the dyadic double-step law restores
-- the required ε(n) output modulus.

record FastCauchyAdditiveLaws (A : RationalMetricAuthority) : Set₁ where
  field
    negDifferenceAbs : ∀ a b →
      absQ A (_-Q_ A (negQ A a) (negQ A b))
      ≡ absQ A (_-Q_ A a b)

    addDifferenceBound : ∀ a b c d →
      _≤Q_ A
        (absQ A
          (_-Q_ A
            (_+Q_ A a b)
            (_+Q_ A c d)))
        (_+Q_ A
          (absQ A (_-Q_ A a c))
          (absQ A (_-Q_ A b d)))

    doublePairError : ∀ m n →
      _+Q_ A
        (_+Q_ A (dyadicError A (suc m)) (dyadicError A (suc n)))
        (_+Q_ A (dyadicError A (suc m)) (dyadicError A (suc n)))
      ≡ _+Q_ A (dyadicError A m) (dyadicError A n)

open FastCauchyAdditiveLaws public

n≤sucn : ∀ n → n ≤ suc n
n≤sucn zero = z≤n
n≤sucn (suc n) = s≤s (n≤sucn n)

≤N-stepRight : ∀ {a b} → a ≤ b → a ≤ suc b
≤N-stepRight a≤b = ≤N-trans a≤b (n≤sucn _)

------------------------------------------------------------------------
-- Negation is pointwise and preserves the exact modulus.

fastNeg :
  ∀ {A : RationalMetricAuthority} →
  FastCauchyAdditiveLaws A →
  FastCauchyReal A →
  FastCauchyReal A
fastNeg {A} laws x =
  fastReal
    (λ n → negQ A (approximate x n))
    negIsFast
  where
    negIsFast : ∀ m n →
      _≤Q_ A
        (absQ A
          (_-Q_ A
            (negQ A (approximate x m))
            (negQ A (approximate x n))))
        (_+Q_ A (dyadicError A m) (dyadicError A n))
    negIsFast m n =
      subst
        (λ lower →
          _≤Q_ A lower
            (_+Q_ A (dyadicError A m) (dyadicError A n)))
        (negDifferenceAbs laws (approximate x m) (approximate x n))
        (fastCauchy x m n)

fastNegRespect :
  ∀ {A : RationalMetricAuthority}
    (laws : FastCauchyAdditiveLaws A)
    {x y : FastCauchyReal A} →
  x ≈R y →
  fastNeg laws x ≈R fastNeg laws y
fastNegRespect {A} laws x≈y precision with x≈y precision
... | cutoff , close =
  cutoff , λ m n cutoff≤m cutoff≤n →
    subst
      (λ lower → _≤Q_ A lower (dyadicError A precision))
      (negDifferenceAbs laws (approximate x m) (approximate y n))
      (close m n cutoff≤m cutoff≤n)

------------------------------------------------------------------------
-- Precision-safe addition.

fastAdd :
  ∀ {A : RationalMetricAuthority} →
  FastCauchyAdditiveLaws A →
  FastCauchyReal A →
  FastCauchyReal A →
  FastCauchyReal A
fastAdd {A} laws x y =
  fastReal
    (λ n →
      _+Q_ A
        (approximate x (suc n))
        (approximate y (suc n)))
    addIsFast
  where
    addIsFast : ∀ m n →
      _≤Q_ A
        (absQ A
          (_-Q_ A
            (_+Q_ A
              (approximate x (suc m))
              (approximate y (suc m)))
            (_+Q_ A
              (approximate x (suc n))
              (approximate y (suc n)))))
        (_+Q_ A (dyadicError A m) (dyadicError A n))
    addIsFast m n =
      leTrans A
        (addDifferenceBound laws
          (approximate x (suc m))
          (approximate y (suc m))
          (approximate x (suc n))
          (approximate y (suc n)))
        (subst
          (λ upper →
            _≤Q_ A
              (_+Q_ A
                (absQ A
                  (_-Q_ A
                    (approximate x (suc m))
                    (approximate x (suc n))))
                (absQ A
                  (_-Q_ A
                    (approximate y (suc m))
                    (approximate y (suc n)))))
              upper)
          (doublePairError laws m n)
          (addMono A
            (fastCauchy x (suc m) (suc n))
            (fastCauchy y (suc m) (suc n))))

fastAddRespect :
  ∀ {A : RationalMetricAuthority}
    (laws : FastCauchyAdditiveLaws A)
    {x x′ y y′ : FastCauchyReal A} →
  x ≈R x′ →
  y ≈R y′ →
  fastAdd laws x y ≈R fastAdd laws x′ y′
fastAddRespect {A} laws x≈x′ y≈y′ precision
  with x≈x′ (suc precision) | y≈y′ (suc precision)
... | cutoffX , closeX | cutoffY , closeY =
  common , closeSum
  where
    common : Nat
    common = maxN cutoffX cutoffY

    cutoffX≤common : cutoffX ≤ common
    cutoffX≤common = left≤max cutoffX cutoffY

    cutoffY≤common : cutoffY ≤ common
    cutoffY≤common = right≤max cutoffX cutoffY

    closeSum : ∀ m n → common ≤ m → common ≤ n →
      _≤Q_ A
        (absQ A
          (_-Q_ A
            (_+Q_ A
              (approximate x (suc m))
              (approximate y (suc m)))
            (_+Q_ A
              (approximate x′ (suc n))
              (approximate y′ (suc n)))))
        (dyadicError A precision)
    closeSum m n common≤m common≤n =
      leTrans A
        (addDifferenceBound laws
          (approximate x (suc m))
          (approximate y (suc m))
          (approximate x′ (suc n))
          (approximate y′ (suc n)))
        (subst
          (λ upper →
            _≤Q_ A
              (_+Q_ A
                (absQ A
                  (_-Q_ A
                    (approximate x (suc m))
                    (approximate x′ (suc n))))
                (absQ A
                  (_-Q_ A
                    (approximate y (suc m))
                    (approximate y′ (suc n)))))
              upper)
          (dyadicDoubleStep A precision)
          (addMono A
            (closeX
              (suc m) (suc n)
              (≤N-stepRight (≤N-trans cutoffX≤common common≤m))
              (≤N-stepRight (≤N-trans cutoffX≤common common≤n)))
            (closeY
              (suc m) (suc n)
              (≤N-stepRight (≤N-trans cutoffY≤common common≤m))
              (≤N-stepRight (≤N-trans cutoffY≤common common≤n)))))

fastSub :
  ∀ {A : RationalMetricAuthority} →
  FastCauchyAdditiveLaws A →
  FastCauchyReal A →
  FastCauchyReal A →
  FastCauchyReal A
fastSub laws x y = fastAdd laws x (fastNeg laws y)

fastSubRespect :
  ∀ {A : RationalMetricAuthority}
    (laws : FastCauchyAdditiveLaws A)
    {x x′ y y′ : FastCauchyReal A} →
  x ≈R x′ →
  y ≈R y′ →
  fastSub laws x y ≈R fastSub laws x′ y′
fastSubRespect laws x≈x′ y≈y′ =
  fastAddRespect laws x≈x′ (fastNegRespect laws y≈y′)

------------------------------------------------------------------------
-- Multiplication and reciprocal require quantitative magnitude/separation data.
-- These records expose the exact nontrivial leaves instead of making pointwise
-- multiplication appear modulus-preserving when it is not.

record BoundedFastCauchy
  {A : RationalMetricAuthority}
  (x : FastCauchyReal A) : Set₁ where
  field
    bound : Q A
    boundNonnegative : _≤Q_ A (zeroQ A) bound
    bounded : ∀ n → _≤Q_ A (absQ A (approximate x n)) bound

open BoundedFastCauchy public

record FastCauchyMultiplicationAuthority
  (A : RationalMetricAuthority)
  (laws : FastCauchyAdditiveLaws A) : Set₁ where
  field
    boundedness : (x : FastCauchyReal A) → BoundedFastCauchy x
    multiply : FastCauchyReal A → FastCauchyReal A → FastCauchyReal A
    multiplyRespect : ∀ {x x′ y y′} →
      x ≈R x′ → y ≈R y′ → multiply x y ≈R multiply x′ y′
    multiplyRepresentsPointwiseProduct : ∀ x y precision →
      Σ Nat
        (λ cutoff →
          ∀ n → cutoff ≤ n →
          _≤Q_ A
            (absQ A
              (_-Q_ A
                (approximate (multiply x y) n)
                (_*Q_ A (approximate x n) (approximate y n))))
            (dyadicError A precision))

open FastCauchyMultiplicationAuthority public

record SeparatedFromZero
  {A : RationalMetricAuthority}
  (x : FastCauchyReal A) : Set₁ where
  field
    separation : Q A
    separationPositive : Set
    cutoff : Nat
    eventuallySeparated : ∀ n → cutoff ≤ n → Set

open SeparatedFromZero public

record FastCauchyReciprocalAuthority
  (A : RationalMetricAuthority)
  (M : FastCauchyMultiplicationAuthority A) : Set₁ where
  field
    reciprocal : (x : FastCauchyReal A) → SeparatedFromZero x → FastCauchyReal A
    reciprocalRespect : ∀ {x y} →
      x ≈R y →
      (sx : SeparatedFromZero x) →
      (sy : SeparatedFromZero y) →
      reciprocal x sx ≈R reciprocal y sy
    reciprocalInverse : ∀ x sx →
      multiply M x (reciprocal x sx) ≈R constantFastReal A (oneQ A)

open FastCauchyReciprocalAuthority public

record FastCauchyDiagonalCompleteness
  (A : RationalMetricAuthority) : Set₁ where
  field
    RealSequence : Set
    sequenceAtReal : RealSequence → Nat → FastCauchyReal A
    IsCauchySequence : RealSequence → Set
    diagonalLimit : (s : RealSequence) → IsCauchySequence s → FastCauchyReal A
    convergesToDiagonal : ∀ s cs → Set
    diagonalIndependent : ∀ s cs₁ cs₂ →
      diagonalLimit s cs₁ ≈R diagonalLimit s cs₂

open FastCauchyDiagonalCompleteness public
