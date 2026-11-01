module DASHI.Foundations.UltrametricAdmissibilityConcentration where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_; _≤?_)
open import Data.Nat.Properties as NatP
open import Relation.Nullary using (Dec)

import Ultrametric as UMetric

------------------------------------------------------------------------
-- Admissibility concentration around a distinguished fixed point.
--
-- The theorem surface deliberately separates:
--   * the ultrametric carrier,
--   * the kernel dynamics,
--   * the quantitative concentration law.
--
-- It does not assert that every physical RG, decoherence, or vacuum-selection
-- process instantiates this record.  Concrete physics lanes must supply the
-- contraction fields.

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate K zero x = x
iterate K (suc n) x = K (iterate K n x)

Ball :
  ∀ {S : Set} →
  UMetric.Ultrametric S →
  S →
  Nat →
  S →
  Set
Ball U centre radius x = UMetric.Ultrametric.d U centre x ≤ radius

ballMembership? :
  ∀ {S : Set}
    (U : UMetric.Ultrametric S)
    (centre : S)
    (radius : Nat)
    (x : S) →
  Dec (Ball U centre radius x)
ballMembership? U centre radius x =
  UMetric.Ultrametric.d U centre x ≤? radius

record AdmissibilityConcentrationKernel
    {S : Set}
    (U : UMetric.Ultrametric S)
    (K : S → S) : Set where
  open UMetric.Ultrametric U

  field
    fixedPoint : S
    fixed : K fixedPoint ≡ fixedPoint

    -- Every application stays at least as close to the selected fixed point.
    contractsToFixed :
      ∀ x →
      d fixedPoint (K x) ≤ d fixedPoint x

    -- Concrete lanes may additionally prove strict contraction away from the
    -- fixed point.  The monotone theorems below do not assume strictness.
    strictlyContractsOffFixed :
      ∀ x →
      fixedPoint ≢ x →
      d fixedPoint (K x) < d fixedPoint x

open AdmissibilityConcentrationKernel public

------------------------------------------------------------------------
-- The monotone/nested consequences require only contractsToFixed.

iterate-step-distance-monotone :
  ∀ {S : Set}
    {U : UMetric.Ultrametric S}
    {K : S → S}
    (C : AdmissibilityConcentrationKernel U K)
    (n : Nat)
    (x : S) →
  UMetric.Ultrametric.d U
    (fixedPoint C)
    (iterate K (suc n) x)
  ≤
  UMetric.Ultrametric.d U
    (fixedPoint C)
    (iterate K n x)
iterate-step-distance-monotone C n x =
  contractsToFixed C (iterate _ n x)

iterate-distance-bounded :
  ∀ {S : Set}
    {U : UMetric.Ultrametric S}
    {K : S → S}
    (C : AdmissibilityConcentrationKernel U K)
    (n : Nat)
    (x : S) →
  UMetric.Ultrametric.d U
    (fixedPoint C)
    (iterate K n x)
  ≤
  UMetric.Ultrametric.d U
    (fixedPoint C)
    x
iterate-distance-bounded C zero x = NatP.≤-refl
iterate-distance-bounded C (suc n) x =
  NatP.≤-trans
    (contractsToFixed C (iterate _ n x))
    (iterate-distance-bounded C n x)

ball-closed-under-kernel :
  ∀ {S : Set}
    {U : UMetric.Ultrametric S}
    {K : S → S}
    (C : AdmissibilityConcentrationKernel U K)
    (radius : Nat)
    {x : S} →
  Ball U (fixedPoint C) radius x →
  Ball U (fixedPoint C) radius (K x)
ball-closed-under-kernel C radius x∈ball =
  NatP.≤-trans (contractsToFixed C _) x∈ball

ball-closed-under-iteration :
  ∀ {S : Set}
    {U : UMetric.Ultrametric S}
    {K : S → S}
    (C : AdmissibilityConcentrationKernel U K)
    (radius n : Nat)
    {x : S} →
  Ball U (fixedPoint C) radius x →
  Ball U (fixedPoint C) radius (iterate K n x)
ball-closed-under-iteration C radius n x∈ball =
  NatP.≤-trans (iterate-distance-bounded C n _) x∈ball

------------------------------------------------------------------------
-- A finite-depth concentration receipt records the exact radius reached by
-- an orbit.  It is intentionally evidence-carrying rather than postulated.

record FiniteDepthConcentration
    {S : Set}
    {U : UMetric.Ultrametric S}
    {K : S → S}
    (C : AdmissibilityConcentrationKernel U K)
    (start : S)
    (depth radius : Nat) : Set where
  field
    reachedBall :
      Ball U (fixedPoint C) radius (iterate K depth start)

    noRadiusIncrease :
      radius ≤ UMetric.Ultrametric.d U (fixedPoint C) start

open FiniteDepthConcentration public

concentration-persists :
  ∀ {S : Set}
    {U : UMetric.Ultrametric S}
    {K : S → S}
    {C : AdmissibilityConcentrationKernel U K}
    {start : S}
    {depth radius : Nat} →
  FiniteDepthConcentration C start depth radius →
  ∀ extra →
  Ball U
    (fixedPoint C)
    radius
    (iterate K extra (iterate K depth start))
concentration-persists receipt extra =
  ball-closed-under-iteration _ _ extra (reachedBall receipt)
