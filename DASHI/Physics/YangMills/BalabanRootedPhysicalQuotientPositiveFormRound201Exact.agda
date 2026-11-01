module DASHI.Physics.YangMills.BalabanRootedPhysicalQuotientPositiveFormRound201Exact where

------------------------------------------------------------------------
-- ROUND 201
--
-- Positive-form producer interface on the same rooted physical carrier.
--
-- This is intentionally downstream of the finite rooted-normal-form theorem
-- and upstream of any completion.  It records the strongest reusable fact:
-- a positive sesquilinear/pre-Hilbert form can be attached directly to rooted
-- representatives, and its null predicate is exactly zero norm.  Therefore
-- the only remaining analytic payment is a producer for this record from the
-- physical Haar/Gibbs state; quotient bookkeeping is finished.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

record RootedPositiveForm
    (Rooted Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    inner : Rooted → Rooted → Scalar

    Positive : Scalar → Set

    hermitianDiagonal :
      ∀ x → Positive (inner x x)

    Null : Rooted → Set
    nullIffZeroDiagonal :
      ∀ x → Null x ≡ (inner x x ≡ zero)

open RootedPositiveForm public

normSquared :
  ∀ {Rooted Scalar} → RootedPositiveForm Rooted Scalar → Rooted → Scalar
normSquared form x = inner form x x

rootedNullIsZeroNorm :
  ∀ {Rooted Scalar}
    (form : RootedPositiveForm Rooted Scalar)
    (x : Rooted) →
  Null form x ≡ (normSquared form x ≡ zero form)
rootedNullIsZeroNorm = nullIffZeroDiagonal

-- This is the exact BIDI terminal frontier: once the physical state supplies
-- this form on the rooted carrier, the GNS null quotient can reuse the same
-- representative object rather than introducing another physical quotient.
record PhysicalStatePositiveFormProducer
    (PhysicalState Rooted Scalar : Set) : Set₁ where
  field
    state : PhysicalState
    form : RootedPositiveForm Rooted Scalar

open PhysicalStatePositiveFormProducer public

producerSuppliesPositiveDiagonal :
  ∀ {PhysicalState Rooted Scalar}
    (producer : PhysicalStatePositiveFormProducer
      PhysicalState Rooted Scalar)
    (x : Rooted) →
  Positive (form producer) (normSquared (form producer) x)
producerSuppliesPositiveDiagonal producer x =
  hermitianDiagonal (form producer) x
