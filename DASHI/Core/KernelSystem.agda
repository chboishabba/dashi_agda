{-# OPTIONS --safe #-}
module DASHI.Core.KernelSystem where

open import Agda.Builtin.Equality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Equivalence relation used for quotient semantics.

record Equivalence {S : Set} (_≈_ : S → S → Set) : Set₁ where
  field
    reflexive : ∀ s → s ≈ s
    symmetric : ∀ {x y} → x ≈ y → y ≈ x
    transitive : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
open Equivalence public

------------------------------------------------------------------------
-- Canonical kernel object.
--
-- Geometry, neighbourhood data, channel structure, and weights are carried as
-- typed parameters instead of being silently baked into an endofunction.

record KernelSystem : Set₂ where
  field
    State : Set
    Site : Set
    Channel : Set
    Geometry : Set
    Neighbourhood : Set
    WeightFamily : Set

    geometry : Geometry
    neighbourhood : Neighbourhood
    weights : WeightFamily

    involution : State → State
    kernel : State → State

    involution-involutive : ∀ s → involution (involution s) ≡ s
    kernel-involution-equivariant :
      ∀ s → kernel (involution s) ≡ involution (kernel s)
open KernelSystem public

------------------------------------------------------------------------
-- Synchronous and scheduled implementations.
--
-- `kernel` is the canonical synchronous transition.  Every scheduled variant
-- is explicit and no convergence property is transferred automatically.

record ScheduledKernel (K : KernelSystem) : Set₁ where
  open KernelSystem K
  field
    Schedule : Set
    canonicalSchedule : Schedule
    scheduled : Schedule → State → State
    canonical-is-synchronous :
      ∀ s → scheduled canonicalSchedule s ≡ kernel s
open ScheduledKernel public

------------------------------------------------------------------------
-- Quotient-respecting kernels.

record QuotientKernel (K : KernelSystem) : Set₁ where
  open KernelSystem K
  field
    _≈_ : State → State → Set
    equivalence : Equivalence _≈_
    respects-quotient :
      ∀ {x y} → x ≈ y → kernel x ≈ kernel y
open QuotientKernel public

record QuotientReadout (K : KernelSystem) : Set₁ where
  open KernelSystem K
  field
    Quotient : Set
    quotient : State → Quotient
open QuotientReadout public

record ReadoutCompleteForRelation
  (K : KernelSystem)
  (QK : QuotientKernel K)
  (QR : QuotientReadout K) : Set₁ where
  open KernelSystem K
  open QuotientKernel QK
  open QuotientReadout QR
  field
    relation⇒same-readout :
      ∀ {x y} → x ≈ y → quotient x ≡ quotient y
open ReadoutCompleteForRelation public

quotient-step-congruence :
  ∀ {K : KernelSystem}
    (QK : QuotientKernel K)
    (QR : QuotientReadout K)
    (complete : ReadoutCompleteForRelation K QK QR)
    {x y} →
  QuotientKernel._≈_ QK x y →
  QuotientReadout.quotient QR (KernelSystem.kernel K x)
    ≡ QuotientReadout.quotient QR (KernelSystem.kernel K y)
quotient-step-congruence QK QR complete related =
  ReadoutCompleteForRelation.relation⇒same-readout complete
    (QuotientKernel.respects-quotient QK related)
