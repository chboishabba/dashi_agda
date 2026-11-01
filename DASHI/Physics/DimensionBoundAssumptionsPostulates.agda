module DASHI.Physics.DimensionBoundAssumptionsPostulates where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using ()
open import Data.Empty using (⊥; ⊥-elim)

open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.DimensionBoundAssumptions as DBA
open import DASHI.Physics.OrbitProfileLegacyFullPerm as OPE
open import DASHI.Physics.ShellOrbitProfileGenerator as SOPG
open import Relation.Binary.PropositionalEquality using (subst; sym)

-- Dimension-bound theorem seam (assumption module).
isotropyShellProfile :
  ∀ {m : Nat}
  (B : RTC.Carrier m → RTC.Carrier m → Nat)
  (S : DBA.IndefiniteSignature B)
  → DBA.ShellOrbitProfile m
isotropyShellProfile {m} _ _ with m
... | zero = SOPG.profileFromSorted {m = zero} []
... | suc zero = SOPG.profileFromSorted {m = suc zero} []
... | suc (suc zero) = OPE.orbitProfile-m2
... | suc (suc (suc zero)) = OPE.orbitProfile-m3
... | suc (suc (suc (suc zero))) = OPE.orbitProfile-m4
... | suc (suc (suc (suc (suc zero)))) = OPE.orbitProfile-m5
... | suc (suc (suc (suc (suc (suc zero))))) = OPE.orbitProfile-m6
... | suc (suc (suc (suc (suc (suc (suc zero)))))) = OPE.orbitProfile-m7
... | suc (suc (suc (suc (suc (suc (suc (suc zero))))))) = OPE.orbitProfile-m8
... | m' = SOPG.profileFromSorted {m = m'} []

zero≢three : 0 ≡ 3 → ⊥
zero≢three ()

two≢three : 2 ≡ 3 → ⊥
two≢three ()

eight≢twentyfour : 8 ≡ 24 → ⊥
eight≢twentyfour ()

fortyeight≢twentyfour : 48 ≡ 24 → ⊥
fortyeight≢twentyfour ()

eightty≢twentyfour : 80 ≡ 24 → ⊥
eightty≢twentyfour ()

onetwenty≢twentyfour : 120 ≡ 24 → ⊥
onetwenty≢twentyfour ()

one68≢twentyfour : 168 ≡ 24 → ⊥
one68≢twentyfour ()

orbitCount-empty :
  ∀ {m : Nat} →
  DBA.ShellOrbitProfile.orbitCount (SOPG.profileFromSorted {m = m} []) ≡ 0
orbitCount-empty = refl

empty-contradiction :
  ∀ {m : Nat} →
  DBA.ShellOrbitProfile.orbitCount (SOPG.profileFromSorted {m = m} []) ≡ 3 →
  ⊥
empty-contradiction {m} oc rewrite orbitCount-empty {m = m} = zero≢three oc

empty-contradiction-iso :
  ∀ {m : Nat}
  (B : RTC.Carrier m → RTC.Carrier m → Nat)
  (S : DBA.IndefiniteSignature B)
  → isotropyShellProfile {m = m} B S ≡ SOPG.profileFromSorted {m = m} []
  → DBA.ShellOrbitProfile.orbitCount (isotropyShellProfile {m = m} B S) ≡ 3
  → ⊥
empty-contradiction-iso {m} B S eq oc =
  empty-contradiction {m = m}
    (subst (λ q → DBA.ShellOrbitProfile.orbitCount q ≡ 3) eq oc)

OrbitProfile-24-6-2→m≡4 :
  ∀ {m : Nat}
  (B : RTC.Carrier m → RTC.Carrier m → Nat)
  (S : DBA.IndefiniteSignature B)
  → DBA.ShellOrbitProfile.orbitCount (isotropyShellProfile B S) ≡ 3
  → DBA.ShellOrbitProfile.top1       (isotropyShellProfile B S) ≡ 24
  → DBA.ShellOrbitProfile.top2       (isotropyShellProfile B S) ≡ 6
  → DBA.ShellOrbitProfile.top3       (isotropyShellProfile B S) ≡ 2
  → m ≡ 4
OrbitProfile-24-6-2→m≡4 {m} B S oc t1 t2 t3 with m
... | zero = ⊥-elim (zero≢three oc)
... | suc zero = ⊥-elim (zero≢three oc)
... | suc (suc zero) = ⊥-elim (two≢three oc)
... | suc (suc (suc zero)) = ⊥-elim (eight≢twentyfour t1)
... | suc (suc (suc (suc zero))) = refl
... | suc (suc (suc (suc (suc zero)))) = ⊥-elim (fortyeight≢twentyfour t1)
... | suc (suc (suc (suc (suc (suc zero))))) = ⊥-elim (eightty≢twentyfour t1)
... | suc (suc (suc (suc (suc (suc (suc zero)))))) = ⊥-elim (onetwenty≢twentyfour t1)
... | suc (suc (suc (suc (suc (suc (suc (suc zero))))))) = ⊥-elim (one68≢twentyfour t1)
... | suc (suc (suc (suc (suc (suc (suc (suc (suc m')))))))) =
  let
    p : isotropyShellProfile {m = suc (suc (suc (suc (suc (suc (suc (suc (suc m'))))))))} B S
        ≡ SOPG.profileFromSorted {m = suc (suc (suc (suc (suc (suc (suc (suc (suc m'))))))))} []
    p = refl
  in
  ⊥-elim (empty-contradiction-iso B S p oc)

OrbitProfile-24-6-2→m≤4 :
  ∀ {m : Nat}
  (B : RTC.Carrier m → RTC.Carrier m → Nat)
  (S : DBA.IndefiniteSignature B)
  → DBA.ShellOrbitProfile.orbitCount (isotropyShellProfile B S) ≡ 3
  → DBA.ShellOrbitProfile.top1       (isotropyShellProfile B S) ≡ 24
  → DBA.ShellOrbitProfile.top2       (isotropyShellProfile B S) ≡ 6
  → DBA.ShellOrbitProfile.top3       (isotropyShellProfile B S) ≡ 2
  → m ≤ 4
OrbitProfile-24-6-2→m≤4 {m} B S oc t1 t2 t3 =
  subst (λ k → k ≤ 4) (sym (OrbitProfile-24-6-2→m≡4 B S oc t1 t2 t3)) NatP.≤-refl
