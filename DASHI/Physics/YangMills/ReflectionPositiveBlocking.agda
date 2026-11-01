module DASHI.Physics.YangMills.ReflectionPositiveBlocking where

------------------------------------------------------------------------
-- Reflection positivity descends along any blocking whose coarse OS form is
-- the pullback of a reflection-positive fine OS form.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.FiniteReflectionPositivity

record ReflectionPositiveBlocking
    (FineObservable CoarseObservable Scalar : Set)
    (scalar : PositiveAdditiveScalar Scalar)
    (fine : FiniteReflectionPositive FineObservable Scalar scalar) : Set₁ where
  field
    liftObservable : CoarseObservable → FineObservable
    coarseOSForm : CoarseObservable → Scalar
    coarseFormPullback : ∀ observable →
      coarseOSForm observable ≡
      FiniteReflectionPositive.osForm fine (liftObservable observable)

open ReflectionPositiveBlocking public

coarseReflectionPositive :
  ∀ {FineObservable CoarseObservable Scalar : Set}
    {scalar : PositiveAdditiveScalar Scalar}
    {fine : FiniteReflectionPositive FineObservable Scalar scalar} →
  (blocking : ReflectionPositiveBlocking
    FineObservable CoarseObservable Scalar scalar fine) →
  ∀ observable →
  Nonnegative scalar (coarseOSForm blocking observable)
coarseReflectionPositive {scalar = scalar} {fine = fine} blocking observable =
  subst
    (Nonnegative scalar)
    (sym (coarseFormPullback blocking observable))
    (reflectionPositive fine (liftObservable blocking observable))

blockedReflectionPositive :
  ∀ {FineObservable CoarseObservable Scalar : Set}
    {scalar : PositiveAdditiveScalar Scalar}
    {fine : FiniteReflectionPositive FineObservable Scalar scalar} →
  ReflectionPositiveBlocking
    FineObservable CoarseObservable Scalar scalar fine →
  FiniteReflectionPositive CoarseObservable Scalar scalar
blockedReflectionPositive blocking = record
  { osForm = coarseOSForm blocking
  ; reflectionPositive = coarseReflectionPositive blocking
  }

reflectionPositiveBlockingLevel : ProofLevel
reflectionPositiveBlockingLevel = machineChecked

reflectionPositivePullbackInputLevel : ProofLevel
reflectionPositivePullbackInputLevel = conditional
