module DASHI.Geometry.RealIsotropyInstanceShift where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_; _xor_)
open import Data.Bool.Properties as BoolP
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Geometry.RealIsotropy as RIS
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.RealOperatorStackShift as ROSS
open import DASHI.Physics.CanonicalizationMinimal as CM
open import DASHI.Physics.TailCollapseInvolution as TCI
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import Ultrametric as UMetric

-- Two-element group acting by invVec.
boolGroup : Iso.Group Bool
boolGroup =
  record
    { _∙_ = _xor_
    ; e = false
    ; inv = λ a → a
    ; assoc = BoolP.xor-assoc
    ; idL = BoolP.xor-identityˡ
    ; invL = BoolP.xor-same
    }

act : ∀ {n} → Bool → RTC.Carrier n → RTC.Carrier n
act {n} b x = if b then RTC.invVec x else x

preservesMetric :
  ∀ {n} → (g : Bool) → (x y : RTC.Carrier n) →
  UMetric.Ultrametric.d (FAM.ultrametricVec {n = n}) (act g x) (act g y)
    ≡ UMetric.Ultrametric.d (FAM.ultrametricVec {n = n}) x y
preservesMetric {n} false x y = refl
preservesMetric {n} true x y = FAM.dNatFine-inv x y

commutesWithT :
  ∀ {m k : Nat} → (g : Bool) → (x : RTC.Carrier (m + k)) →
  ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} (act g x)))
    ≡ act g (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
commutesWithT {m} {k} false x = refl
commutesWithT {m} {k} true x =
  let
    step1 : ROSS.R {m} {k} (RTC.invVec x) ≡ RTC.invVec (ROSS.R {m} {k} x)
    step1 = sym (TCI.invVec-Rᵣ {m} {k} x)
    step2 : ROSS.P {m} {k} (RTC.invVec (ROSS.R {m} {k} x))
            ≡ RTC.invVec (ROSS.P {m} {k} (ROSS.R {m} {k} x))
    step2 = sym (TCI.invVec-Pᵣ {m} {k} (ROSS.R {m} {k} x))
    step3 : ROSS.C {m} {k} (RTC.invVec (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
            ≡ RTC.invVec (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
    step3 = sym (CM.Cᵣ-invVec {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
  in
  trans
    (cong (λ v → ROSS.C {m} {k} (ROSS.P {m} {k} v)) step1)
    (trans (cong (λ v → ROSS.C {m} {k} v) step2) step3)

realIsotropyInstanceShift :
  ∀ {m k : Nat} →
  RIS.RealIsotropy (FAM.ultrametricVec {n = m + k})
    (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
realIsotropyInstanceShift {m} {k} =
  record
    { iso =
        record
          { G = Bool
          ; group = boolGroup
          ; act = act
          ; preservesMetric = preservesMetric
          ; commutesWithT = commutesWithT {m} {k}
          }
    ; coneInvariant = Bool
    }
