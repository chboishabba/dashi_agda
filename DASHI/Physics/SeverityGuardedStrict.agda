module DASHI.Physics.SeverityGuardedStrict where

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Ultrametric as UMetric
open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Physics.SeverityGuard as SG using (SeverityPolicy; Guard; Broken; Snap)
open import DASHI.Physics.TailCollapseGuardedStrict as TG

-- Adapter: build Guard/Broken/Snap from a SeverityPolicy, while leaving
-- Restore/P/proj abstract for the concrete instance.
record SeverityGuardedStrict : Set₁ where
  field
    S : Set
    policy : SG.SeverityPolicy S

    Uₛ : UMetric.Ultrametric S
    Pₛ : S → S
    Restoreₛ : S → S

    P-strict-onₛ :
      ∀ {x y} →
      SG.Guard policy x → SG.Guard policy y →
      FC.FiberDistinct Pₛ x y →
      UMetric.Ultrametric.d Uₛ (Pₛ x) (Pₛ y) < UMetric.Ultrametric.d Uₛ x y

    restore-normal-formₛ :
      ∀ x → SG.Broken policy x → SG.Guard policy (Restoreₛ x)

    restore-idemₛ :
      ∀ x → Restoreₛ (Restoreₛ x) ≡ Restoreₛ x

    restore-fixesₛ :
      ∀ x → Pₛ (Restoreₛ x) ≡ Restoreₛ x

  toGuardedStrict : TG.GuardedStrictness
  toGuardedStrict =
    let p = policy in
    record
      { X = S
      ; U = Uₛ
      ; P = Pₛ
      ; Guard = SG.SeverityPolicy.Guard p
      ; Broken = SG.SeverityPolicy.Broken p
      ; Snap = SG.SeverityPolicy.Snap p
      ; Restore = Restoreₛ
      ; P-strict-on = λ {x} {y} gx gy fd → P-strict-onₛ {x = x} {y = y} gx gy fd
      ; restore-normal-form = restore-normal-formₛ
      ; restore-idem = restore-idemₛ
      ; restore-fixes = restore-fixesₛ
      }

open SeverityGuardedStrict public
