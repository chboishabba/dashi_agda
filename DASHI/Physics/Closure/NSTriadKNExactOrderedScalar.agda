module DASHI.Physics.Closure.NSTriadKNExactOrderedScalar where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact

------------------------------------------------------------------------
-- Ordered scalar authority for the symbolic NS shell operator.
--
-- This is deliberately weaker than a completed real-analysis or spectral
-- library.  In particular, no completeness or inverse-square-root theorem is
-- assumed here.  It gives exactly the algebraic order facts needed to form
-- the absolute/negative Gram coefficients for arbitrary Fourier data.
------------------------------------------------------------------------

record ExactOrderedScalar : Set₁ where
  constructor mkExactOrderedScalar
  field
    Scalar : Set

    zero one : Scalar
    _+_ _*_ : Scalar → Scalar → Scalar
    neg : Scalar → Scalar
    third : Scalar → Scalar
    abs : Scalar → Scalar
    max : Scalar → Scalar → Scalar
    sqrt : Scalar → Scalar
    natToScalar : Nat → Scalar

    _≤_ : Scalar → Scalar → Set
    Nonzero : Scalar → Set
    WithinMinusOneOne : Scalar → Set

    absoluteSplit :
      (x : Scalar) →
      abs x ≡ _+_ (max zero x) (max zero (neg x))

    leftMultiplicationDistributesOverAddition :
      (a b c : Scalar) →
      _*_ a (_+_ b c) ≡ _+_ (_*_ a b) (_*_ a c)

    zeroLeAbs :
      (x : Scalar) → _≤_ zero (abs x)
    negativePartNonnegative :
      (x : Scalar) → _≤_ zero (max zero (neg x))
    negativePartLeAbsolute :
      (x : Scalar) → _≤_ (max zero (neg x)) (abs x)

    multiplicationPreservesNonnegative :
      {a b : Scalar} → _≤_ zero a → _≤_ zero b → _≤_ zero (_*_ a b)
    multiplicationMonotoneNonnegativeRight :
      {a b c : Scalar} → _≤_ zero a → _≤_ b c → _≤_ (_*_ a b) (_*_ a c)
    thirdPreservesNonnegative :
      {a : Scalar} → _≤_ zero a → _≤_ zero (third a)

open ExactOrderedScalar public

Nonnegative : (S : ExactOrderedScalar) → Scalar S → Set
Nonnegative S x = _≤_ S (zero S) x

maxZero : (S : ExactOrderedScalar) → Scalar S → Scalar S
maxZero S x = max S (zero S) x

maxPositive : (S : ExactOrderedScalar) → Scalar S → Scalar S
maxPositive = maxZero

maxNegative : (S : ExactOrderedScalar) → Scalar S → Scalar S
maxNegative S x = max S (zero S) (neg S x)

exactScalarOperations : ExactOrderedScalar → Exact.ExactScalarOperations
exactScalarOperations S =
  record
    { Carrier = Scalar S
    ; zero = zero S
    ; one = one S
    ; _+_ = _+_ S
    ; _*_ = _*_ S
    ; third = third S
    ; maxZero = maxZero S
    ; maxPositive = maxPositive S
    ; maxNegative = maxNegative S
    ; absolute = abs S
    ; sqrt = sqrt S
    ; natToScalar = natToScalar S
    ; Nonnegative = Nonnegative S
    ; WithinMinusOneOne = WithinMinusOneOne S
    ; Nonzero = Nonzero S
    ; absoluteSplit = absoluteSplit S
    ; leftMultiplicationDistributesOverAddition =
        leftMultiplicationDistributesOverAddition S
    }

maxNegativeNonnegative :
  (S : ExactOrderedScalar) → (x : Scalar S) →
  Nonnegative S (maxNegative S x)
maxNegativeNonnegative S x = negativePartNonnegative S x

maxNegativeLeAbs :
  (S : ExactOrderedScalar) → (x : Scalar S) →
  _≤_ S (maxNegative S x) (abs S x)
maxNegativeLeAbs S x = negativePartLeAbsolute S x
