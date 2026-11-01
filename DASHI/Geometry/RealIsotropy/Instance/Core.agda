module DASHI.Geometry.RealIsotropy.Instance.Core where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Bool using (Bool; true; false; if_then_else_; _xor_)
open import Data.Bool.Properties as BoolP
open import DASHI.Geometry.Isotropy as Iso
open import DASHI.Geometry.RealIsotropy.Core as RIS
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.RealOperators as RO
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import Ultrametric as UMetric
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

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
  ∀ {n} → (g : Bool) → (x : RTC.Carrier n) →
  RO.Cᵣ (RO.Pᵣ (RO.Rᵣ (act g x))) ≡ act g (RO.Cᵣ (RO.Pᵣ (RO.Rᵣ x)))
commutesWithT {n} false x = refl
commutesWithT {n} true x =
  -- Cᵣ := Pᵣ, Rᵣ := id. We need: Pᵣ (Pᵣ (invVec x)) = invVec (Pᵣ (Pᵣ x)).
  -- Use commutation of invVec with Pᵣ twice.
  trans
    (cong RO.Pᵣ (sym (RO.invVec-Pᵣ x)))
    (trans
      (sym (RO.invVec-Pᵣ (RO.Pᵣ x)))
      refl)

realIsotropyInstance :
  ∀ {n} →
  RIS.RealIsotropy (FAM.ultrametricVec {n = n}) (λ x → RO.Cᵣ (RO.Pᵣ (RO.Rᵣ x)))
realIsotropyInstance {n} =
  record
    { iso =
        record
          { G = Bool
          ; group = boolGroup
          ; act = act
          ; preservesMetric = preservesMetric
          ; commutesWithT = commutesWithT
          }
    ; coneInvariant = Bool
    }
