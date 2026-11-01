module DASHI.Physics.MaassRestorationShift where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec using (Vec)
open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.LiftToFullState as LFS
open import DASHI.Physics.MaskedQuadraticRenormalization as MQR using (tailOf-++; coarseOf-++)

-- Restoration: preserve coarse trunk and zero the tail.
restoreᵣ : ∀ {m k : Nat} → RTC.Carrier (m + k) → RTC.Carrier (m + k)
restoreᵣ {m} {k} x = LFS.embedCoarse m k (TCP.coarseOf m k x)

-- Tail of a restored state is canonical zeros.
tailOf-restore :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  TCP.tailOf m k (restoreᵣ {m} {k} x) ≡ Data.Vec.replicate k zer
tailOf-restore {m} {k} x =
  MQR.tailOf-++ m k (TCP.coarseOf m k x) (Data.Vec.replicate k zer)

-- Restoration is idempotent.
restore-idem :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  restoreᵣ {m} {k} (restoreᵣ {m} {k} x) ≡ restoreᵣ {m} {k} x
restore-idem {m} {k} x
  rewrite MQR.coarseOf-++ m k (TCP.coarseOf m k x) (Data.Vec.replicate k zer)
  = refl

-- Pᵣ fixes restored states.
restore-fixes :
  ∀ {m k : Nat} (x : RTC.Carrier (m + k)) →
  TCP.Pᵣ {m} {k} (restoreᵣ {m} {k} x) ≡ restoreᵣ {m} {k} x
restore-fixes {m} {k} x
  rewrite TCP.Pᵣ-++ m k (TCP.coarseOf m k x) (Data.Vec.replicate k zer)
        | TCP.projTail-replicate {k}
  = refl
