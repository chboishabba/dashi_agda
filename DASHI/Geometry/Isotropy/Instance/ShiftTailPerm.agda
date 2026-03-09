module DASHI.Geometry.Isotropy.Instance.ShiftTailPerm where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Data.Vec using (Vec)

open import Ultrametric as UMetric
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Geometry.RealIsotropy as RIS
open import DASHI.Geometry.ShiftIsotropyTailPerm as TP
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.RealOperatorStackShift as ROSS

------------------------------------------------------------------------
-- Tail-permutation isotropy instance (axiom record; no postulates).
------------------------------------------------------------------------

act : ∀ {m k : Nat} → TP.Perm k → RTC.Carrier (m + k) → RTC.Carrier (m + k)
act {m} {k} p x = TP.actTailPerm {m} {k} p x

record TailPermIsotropyAxioms {m k : Nat} : Set₁ where
  field
    permGroup : Iso.Group (TP.Perm k)

    preservesMetric :
      ∀ p x y →
      UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k})
        (act {m} {k} p x) (act {m} {k} p y)
        ≡
      UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y

    tailPerm-Rᵣ :
      ∀ (p : TP.Perm k) (x : RTC.Carrier (m + k)) →
        ROSS.R {m} {k} (act p x) ≡ act p (ROSS.R {m} {k} x)

    tailPerm-Pᵣ :
      ∀ (p : TP.Perm k) (x : RTC.Carrier (m + k)) →
        ROSS.P {m} {k} (act p x) ≡ act p (ROSS.P {m} {k} x)

    tailPerm-Cᵣ :
      ∀ (p : TP.Perm k) (x : RTC.Carrier (m + k)) →
        ROSS.C {m} {k} (act p x) ≡ act p (ROSS.C {m} {k} x)

commutesWithT :
  ∀ {m k : Nat} →
  (ax : TailPermIsotropyAxioms {m} {k}) →
  (p : TP.Perm k) → (x : RTC.Carrier (m + k)) →
    ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} (act p x)))
      ≡ act p (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
commutesWithT {m} {k} ax p x =
  TP.commutesWithT-CPR
    (ROSS.R {m} {k})
    (ROSS.P {m} {k})
    (ROSS.C {m} {k})
    p
    (TailPermIsotropyAxioms.tailPerm-Rᵣ ax p)
    (TailPermIsotropyAxioms.tailPerm-Pᵣ ax p)
    (TailPermIsotropyAxioms.tailPerm-Cᵣ ax p)
    x

realIsotropyInstanceShiftTailPerm :
  ∀ {m k : Nat} →
  TailPermIsotropyAxioms {m} {k} →
  RIS.RealIsotropy (FAM.ultrametricVec {n = m + k})
    (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
realIsotropyInstanceShiftTailPerm {m} {k} ax =
  record
    { iso =
        record
          { G = TP.Perm k
          ; group = TailPermIsotropyAxioms.permGroup ax
          ; act = act
          ; preservesMetric = TailPermIsotropyAxioms.preservesMetric ax
          ; commutesWithT = commutesWithT {m} {k} ax
          }
    ; coneInvariant = TP.Perm k
    }
