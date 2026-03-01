module DASHI.Physics.SeverityGuardedStrictFine where

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (Nat; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Physics.SeverityGuard as SG using (SeverityPolicy; Guard; Broken; Snap)
open import DASHI.Physics.TailCollapseGuardedStrictFine as TG

-- Adapter: build Guard/Broken/Snap from a SeverityPolicy, while leaving
-- Restore/P/d abstract for the concrete instance.
record SeverityGuardedStrictFine {ℓ} : Set (lsuc ℓ) where
  field
    S : Set ℓ
    policy : SG.SeverityPolicy S

    Pₛ : S → S
    Restoreₛ : S → S
    dₛ : S → S → Nat

    P-strict-onₛ :
      ∀ {x y} →
      SG.Guard policy x → SG.Guard policy y →
      FC.FiberDistinct Pₛ x y →
      dₛ (Pₛ x) (Pₛ y) < dₛ x y

    restore-normal-formₛ :
      ∀ x → SG.Broken policy x → SG.Guard policy (Restoreₛ x)

    restore-idemₛ :
      ∀ x → Restoreₛ (Restoreₛ x) ≡ Restoreₛ x

    restore-fixesₛ :
      ∀ x → Pₛ (Restoreₛ x) ≡ Restoreₛ x

  toGuardedStrict : TG.GuardedStrictnessFine
  toGuardedStrict =
    let p = policy in
    record
      { X = S
      ; P = Pₛ
      ; d = dₛ
      ; Guard = SG.SeverityPolicy.Guard p
      ; Broken = SG.SeverityPolicy.Broken p
      ; Snap = SG.SeverityPolicy.Snap p
      ; Restore = Restoreₛ
      ; P-strict-on = λ {x} {y} gx gy fd → P-strict-onₛ {x = x} {y = y} gx gy fd
      ; restore-normal-form = restore-normal-formₛ
      ; restore-idem = restore-idemₛ
      ; restore-fixes = restore-fixesₛ
      }

open SeverityGuardedStrictFine public
