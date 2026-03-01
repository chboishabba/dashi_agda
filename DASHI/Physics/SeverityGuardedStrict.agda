module DASHI.Physics.SeverityGuardedStrict where

open import Agda.Primitive using (Level; lsuc)
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Physics.SeverityGuard as SG using (SeverityPolicy; Guard; Broken; Snap)
open import DASHI.Physics.TailCollapseGuardedStrict as TG

-- Adapter: build Guard/Broken/Snap from a SeverityPolicy, while leaving
-- Restore/P/proj abstract for the concrete instance.
record SeverityGuardedStrict {ℓ} {A : Set ℓ} : Set (lsuc ℓ) where
  field
    S : Set ℓ
    policy : SG.SeverityPolicy S

    Pₛ : S → S
    Restoreₛ : S → S
    projₛ : S → Stream A
    κₛ : ℕ

    P-strict-onₛ :
      ∀ {x y k} →
      SG.Guard policy x → SG.Guard policy y →
      lcp≥ (projₛ x) (projₛ y) k →
      lcp≥ (projₛ (Pₛ x)) (projₛ (Pₛ y)) (k + κₛ)

    restore-normal-formₛ :
      ∀ x → SG.Broken policy x → SG.Guard policy (Restoreₛ x)

    restore-idemₛ :
      ∀ x → Restoreₛ (Restoreₛ x) ≡ Restoreₛ x

    restore-fixesₛ :
      ∀ x → Pₛ (Restoreₛ x) ≡ Restoreₛ x

  toGuardedStrict : TG.GuardedStrictness {A = A}
  toGuardedStrict =
    let p = policy in
    record
      { X = S
      ; P = Pₛ
      ; proj = projₛ
      ; Guard = SG.SeverityPolicy.Guard p
      ; Broken = SG.SeverityPolicy.Broken p
      ; Snap = SG.SeverityPolicy.Snap p
      ; Restore = Restoreₛ
    ; κ = κₛ
      ; P-strict-on = λ {x} {y} {k} gx gy hyp → P-strict-onₛ {x = x} {y = y} {k = k} gx gy hyp
      ; restore-normal-form = restore-normal-formₛ
      ; restore-idem = restore-idemₛ
      ; restore-fixes = restore-fixesₛ
      }

open SeverityGuardedStrict public
