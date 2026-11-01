module DASHI.Physics.Closure.EnergyShiftBase where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; z≤n)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans; ≤-antisym)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import DASHI.Energy.Energy as E
open import DASHI.Energy.ClosestPoint as CP
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import Ultrametric as UMetric

-- Preorder over Nat with ≤.
NatPreorder : E.Preorder
NatPreorder = record
  { S = Nat
  ; _≤_ = Data.Nat._≤_
  ; refl≤ = λ _ → NatP.≤-refl
  ; trans≤ = λ _ _ _ → NatP.≤-trans
  }

-- Energy = ultrametric distance.
energy-sep :
  ∀ (m k : Nat) (x y : RTC.Carrier (m + k)) →
  E.Preorder._≤_ NatPreorder
    (UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y)
    (UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x x) →
  x ≡ y
energy-sep m k x y h =
  let
    U = FAM.ultrametricVec {n = m + k}
    dxy = UMetric.Ultrametric.d U x y
    dxx = UMetric.Ultrametric.d U x x
    dxx≡0 = UMetric.Ultrametric.id-zero U x
    h' : dxy Data.Nat.≤ 0
    h' = subst (λ v → dxy Data.Nat.≤ v) dxx≡0 h
    dxy≡0 : dxy ≡ 0
    dxy≡0 = NatP.≤-antisym h' z≤n
  in
  FAM.dNatFine-zero→eq x y dxy≡0

EnergyShift : ∀ {m k : Nat} → E.EnergySpace (RTC.Carrier (m + k)) NatPreorder
EnergyShift {m} {k} =
  record
    { E = UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k})
    ; E-refl = λ _ → NatP.≤-refl
    ; E-sep = energy-sep m k
    }

ProjShift : ∀ {m k : Nat} → CP.Projection (RTC.Carrier (m + k))
ProjShift {m} {k} =
  record
    { P = TCP.Pᵣ {m} {k}
    ; idem = TCP.Pᵣ-idem m k
    }
