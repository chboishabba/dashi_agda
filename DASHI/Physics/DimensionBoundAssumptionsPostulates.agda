module DASHI.Physics.DimensionBoundAssumptionsPostulates where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.DimensionBoundAssumptions as DBA

-- Dimension-bound theorem seam (assumption module).
postulate
  isotropyShellProfile :
    ∀ {m : Nat}
    (B : RTC.Carrier m → RTC.Carrier m → Nat)
    (S : DBA.IndefiniteSignature B)
    → DBA.ShellOrbitProfile m

  OrbitProfile-24-6-2→m≡4 :
    ∀ {m : Nat}
    (B : RTC.Carrier m → RTC.Carrier m → Nat)
    (S : DBA.IndefiniteSignature B)
    → DBA.ShellOrbitProfile.orbitCount (isotropyShellProfile B S) ≡ 3
    → DBA.ShellOrbitProfile.top1       (isotropyShellProfile B S) ≡ 24
    → DBA.ShellOrbitProfile.top2       (isotropyShellProfile B S) ≡ 6
    → DBA.ShellOrbitProfile.top3       (isotropyShellProfile B S) ≡ 2
    → m ≡ 4

  OrbitProfile-24-6-2→m≤4 :
    ∀ {m : Nat}
    (B : RTC.Carrier m → RTC.Carrier m → Nat)
    (S : DBA.IndefiniteSignature B)
    → DBA.ShellOrbitProfile.orbitCount (isotropyShellProfile B S) ≡ 3
    → DBA.ShellOrbitProfile.top1       (isotropyShellProfile B S) ≡ 24
    → DBA.ShellOrbitProfile.top2       (isotropyShellProfile B S) ≡ 6
    → DBA.ShellOrbitProfile.top3       (isotropyShellProfile B S) ≡ 2
    → m ≤ 4

  m≡4→sig≡1+3-up-to-swap :
    ∀ (B : RTC.Carrier 4 → RTC.Carrier 4 → Nat)
      (S : DBA.IndefiniteSignature B)
    → (DBA.IndefiniteSignature.sig S ≡ (1 , 3)) × (DBA.IndefiniteSignature.sig S ≡ (3 , 1))
