module DASHI.Geometry.RealIsotropyInstanceShiftTailPerm where

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
-- Tail-permutation isotropy instance (skeleton).
-- To keep the closure spine postulate-free, do NOT wire this into
-- TernaryRealInstanceShift until the postulates below are discharged.
------------------------------------------------------------------------

postulate
  permGroup : ∀ {k : Nat} → Iso.Group (TP.Perm k)

act : ∀ {m k : Nat} → TP.Perm k → RTC.Carrier (m + k) → RTC.Carrier (m + k)
act {m} {k} p x = TP.actTailPerm {m} {k} p x

postulate
  preservesMetric :
    ∀ {m k : Nat} →
    ∀ p x y →
    UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k})
      (act {m} {k} p x) (act {m} {k} p y)
      ≡
    UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y

  tailPerm-Rᵣ :
    ∀ {m k} (p : TP.Perm k) (x : RTC.Carrier (m + k)) →
      ROSS.R {m} {k} (act p x) ≡ act p (ROSS.R {m} {k} x)

  tailPerm-Pᵣ :
    ∀ {m k} (p : TP.Perm k) (x : RTC.Carrier (m + k)) →
      ROSS.P {m} {k} (act p x) ≡ act p (ROSS.P {m} {k} x)

  tailPerm-Cᵣ :
    ∀ {m k} (p : TP.Perm k) (x : RTC.Carrier (m + k)) →
      ROSS.C {m} {k} (act p x) ≡ act p (ROSS.C {m} {k} x)

commutesWithT :
  ∀ {m k : Nat} → (p : TP.Perm k) → (x : RTC.Carrier (m + k)) →
    ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} (act p x)))
      ≡ act p (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
commutesWithT {m} {k} p x =
  TP.commutesWithT-CPR
    (ROSS.R {m} {k})
    (ROSS.P {m} {k})
    (ROSS.C {m} {k})
    p
    (tailPerm-Rᵣ p)
    (tailPerm-Pᵣ p)
    (tailPerm-Cᵣ p)
    x

realIsotropyInstanceShiftTailPerm :
  ∀ {m k : Nat} →
  RIS.RealIsotropy (FAM.ultrametricVec {n = m + k})
    (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
realIsotropyInstanceShiftTailPerm {m} {k} =
  record
    { iso =
        record
          { G = TP.Perm k
          ; group = permGroup
          ; act = act
          ; preservesMetric = preservesMetric {m} {k}
          ; commutesWithT = commutesWithT {m} {k}
          }
    ; coneInvariant = TP.Perm k
    }
