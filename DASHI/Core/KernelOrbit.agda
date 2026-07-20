{-# OPTIONS --safe #-}
module DASHI.Core.KernelOrbit where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)

open import DASHI.Core.KernelSystem

iterate :
  ∀ {S : Set} →
  Nat →
  (S → S) →
  S → S
iterate zero K s = s
iterate (suc n) K s = iterate n K (K s)

iterate-suc-front :
  ∀ {S : Set}
    (n : Nat)
    (K : S → S)
    (s : S) →
  iterate (suc n) K s ≡ iterate n K (K s)
iterate-suc-front n K s = refl

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
  (q : S → Q)
  (K : S → S)
  (s : S) : Set where
  field
    stableClass : q (K s) ≡ q s
open QuotientStable public

record OrbitClassCollapse
  {S Q : Set}
  (q : S → Q)
  (K : S → S)
  (s : S) : Set where
  field
    everyPhaseSameClass : ∀ n → q (iterate n K s) ≡ q s
open OrbitClassCollapse public

fixedPoint⇒quotientStable :
  ∀ {S Q : Set}
    {K : S → S}
    {q : S → Q}
    {s : S} →
  FixedPoint K s →
  QuotientStable q K s
fixedPoint⇒quotientStable {q = q} fp = record
  { stableClass = cong q (fixed fp) }

quotientStable-everywhere⇒orbitCollapse :
  ∀ {S Q : Set}
    {K : S → S}
    {q : S → Q}
    {s : S} →
  (allStable : ∀ x → q (K x) ≡ q x) →
  OrbitClassCollapse q K s
quotientStable-everywhere⇒orbitCollapse {K = K} {q = q} {s = s} allStable =
  record { everyPhaseSameClass = collapse }
  where
  collapse : ∀ n → q (iterate n K s) ≡ q s
  collapse zero = refl
  collapse (suc n) =
    trans
      (collapse-from-step n)
      (collapse n)

  collapse-from-step : ∀ n → q (iterate (suc n) K s) ≡ q (iterate n K s)
  collapse-from-step zero = allStable s
  collapse-from-step (suc n) = collapse-from-step n

periodicOrbit⇒quotientClosure :
  ∀ {S Q : Set}
    {K : S → S}
    {q : S → Q}
    {s : S} →
  (orbit : PeriodicOrbit K s) →
  q (iterate (suc (predecessorPeriod orbit)) K s) ≡ q s
periodicOrbit⇒quotientClosure {q = q} orbit = cong q (closes orbit)

record EventualPeriodicity
  {S : Set}
  (K : S → S)
  (s : S) : Set where
  field
    preperiod : Nat
    predecessorPeriod : Nat
    repeats :
      iterate (preperiod + suc predecessorPeriod) K s
        ≡ iterate preperiod K s
open EventualPeriodicity public
