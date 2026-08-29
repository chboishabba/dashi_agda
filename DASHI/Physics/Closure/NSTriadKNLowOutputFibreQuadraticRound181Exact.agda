module DASHI.Physics.Closure.NSTriadKNLowOutputFibreQuadraticRound181Exact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Round181: finite-fibre quadratic aggregation without an ℓ¹/cardinality step.
--
-- This is the abstract finite-Hilbert-space shape needed after the Round178
-- pointwise low-output kernel gain.  Instead of bounding |Σ cell| by Σ|cell|,
-- we expose the Gram/Cauchy payment directly on the complete output fibre.
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

foldV : ∀ {C : AdditiveInnerCarrier} →
        (open AdditiveInnerCarrier C in Vec) →
        (open AdditiveInnerCarrier C in Vec → Vec) → Nat →
        (open AdditiveInnerCarrier C in Vec)
foldV {C} seed step zero = seed
foldV {C} seed step (suc n) = AdditiveInnerCarrier._+v_ C (step seed) (foldV {C} seed step n)

-- We keep the finite family proof-bearing.  The decisive estimate is the
-- vector-valued Cauchy/Gram inequality on the already-summed fibre; no theorem
-- here introduces a factor equal to the number of incidences.
record OutputFibreQuadraticPayment (C : AdditiveInnerCarrier) : Set₁ where
  open AdditiveInnerCarrier C
  field
    Fibre : Set
    kernel : Fibre → Vec
    total : Vec
    kernelMass outputWeight : Scalar

    total-is-signed-fibre-sum : Set
    gram-payment : _≤s_ (normSq total) (outputWeight *s kernelMass)

open OutputFibreQuadraticPayment public

-- The physical instantiation is intentionally separated from the abstract
-- quadratic reducer: Round178 supplies the low-output factor at each physical
-- cell; the next owner must prove that its complete same-output fibre satisfies
-- this Gram payment with cutoff-uniform kernelMass.
record PhysicalRound181Frontier : Set₁ where
  field
    AbstractCarrier : AdditiveInnerCarrier
    payment : OutputFibreQuadraticPayment AbstractCarrier
    cutoffUniformKernelMass : Set

-- No Package-A closure token is exported here.  The remaining theorem is the
-- physical cutoff-uniform proof of cutoffUniformKernelMass followed by its
-- trajectory integration.
