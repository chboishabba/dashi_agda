module DASHI.Physics.Closure.NSTriadKNLowOutputFibreQuadraticRound181Exact where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Round181: finite-fibre quadratic aggregation without an ℓ¹/cardinality step.
--
-- Round178 supplies a pointwise low-output kernel mass bound.  The next
-- analytic step must aggregate a complete same-output fibre without replacing
-- |Σ cell| by Σ|cell|.  This module records exactly that quadratic payment
-- shape and nothing stronger.
------------------------------------------------------------------------

record AdditiveInnerCarrier : Set₁ where
  field
    Scalar Vec : Set
    zeroS oneS : Scalar
    _+s_ _*s_ : Scalar → Scalar → Scalar
    _≤s_ : Scalar → Scalar → Set
    zeroV : Vec
    _+v_ : Vec → Vec → Vec
    normSq : Vec → Scalar
    gram : Vec → Vec → Scalar

open AdditiveInnerCarrier public

record OutputFibreQuadraticPayment (C : AdditiveInnerCarrier) : Set₁ where
  open AdditiveInnerCarrier C
  field
    Fibre : Set
    kernel : Fibre → Vec
    total : Vec
    kernelMass outputWeight : Scalar

    -- This witness is intentionally abstract: the physical owner must identify
    -- `total` with the complete signed same-output fibre sum.
    total-is-signed-fibre-sum : Set

    -- Decisive quadratic estimate.  No cardinality factor occurs in the type.
    gram-payment : _≤s_ (normSq total) (outputWeight *s kernelMass)

open OutputFibreQuadraticPayment public

record PhysicalRound181Frontier : Set₁ where
  field
    carrier : AdditiveInnerCarrier
    payment : OutputFibreQuadraticPayment carrier
    cutoffUniformKernelMass : Set

-- No Package-A closure token is exported.  The unresolved physical theorem is
-- the cutoff-uniform proof of `cutoffUniformKernelMass`, followed by the
-- trajectory integration/absorption step.
