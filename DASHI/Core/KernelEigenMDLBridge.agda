{-# OPTIONS --safe #-}
module DASHI.Core.KernelEigenMDLBridge where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import DASHI.MDL.MDLLyapunov

------------------------------------------------------------------------
-- Iteration and eigen-objects.
--
-- Fixed points and finite periodic orbits are kept distinct.  A quotient-
-- stable state need not be a literal fixed point: one kernel step may change
-- the representative while preserving the quotient class.

iterate :
  ∀ {S : Set} →
  Nat →
  (S → S) →
  S → S
iterate zero K s = s
iterate (suc n) K s = iterate n K (K s)

record FixedPoint {S : Set} (K : S → S) (s : S) : Set where
  field
    fixed : K s ≡ s
open FixedPoint public

record PeriodicOrbit {S : Set} (K : S → S) (s : S) : Set where
  field
    predecessorPeriod : Nat
    closes : iterate (suc predecessorPeriod) K s ≡ s
open PeriodicOrbit public

record QuotientStable
  {S Q : Set}
  (quotient : S → Q)
  (K : S → S)
  (s : S) : Set where
  field
    stableClass : quotient (K s) ≡ quotient s
open QuotientStable public

fixedPoint⇒quotientStable :
  ∀ {S Q : Set}
    {K : S → S}
    {quotient : S → Q}
    {s : S} →
  FixedPoint K s →
  QuotientStable quotient K s
fixedPoint⇒quotientStable {quotient = quotient} fp = record
  { stableClass = cong quotient (fixed fp) }

periodicOrbit⇒quotientClosure :
  ∀ {S Q : Set}
    {K : S → S}
    {quotient : S → Q}
    {s : S} →
  (orbit : PeriodicOrbit K s) →
  quotient (iterate (suc (predecessorPeriod orbit)) K s) ≡ quotient s
periodicOrbit⇒quotientClosure {quotient = quotient} orbit =
  cong quotient (closes orbit)

------------------------------------------------------------------------
-- Existing MDL cross-pollination.
--
-- This record does not invent a new Lyapunov notion.  It packages the existing
-- MDLFunctional and MDLLyapunov surfaces around a kernel update.  In
-- particular, no monotonicity claim is made for an unrelated inconsistency
-- diagnostic E(s).

record KernelActionSystem (S : Set) : Set₁ where
  field
    kernel : S → S
    functional : MDLFunctional S
    lyapunov : MDLLyapunov kernel functional
open KernelActionSystem public

kernelMDLMonotone :
  ∀ {S : Set}
    (system : KernelActionSystem S)
    (s : S) →
  MDLFunctional.mdl (functional system) (kernel system s)
    ≤ MDLFunctional.mdl (functional system) s
kernelMDLMonotone system = MDLLyapunov.decreases (lyapunov system)
