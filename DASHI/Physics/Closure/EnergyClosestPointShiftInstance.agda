module DASHI.Physics.Closure.EnergyClosestPointShiftInstance where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Nat using (z≤n; s≤s; _⊔_)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans; ≤-antisym; ⊔-lub)

open import DASHI.Energy.Energy as E
open import DASHI.Energy.ClosestPoint as CP
open import DASHI.Energy.FejerToClosestPoint as FC
open import DASHI.Physics.Closure.ClosestPointAxiomsShift as CPA
open import DASHI.Physics.Closure.EnergyShiftBase as ESB
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.RealOperatorStackShift as ROSS
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import Ultrametric as UMetric

-- Concrete Fejér/ClosestPoint proofs for the shift contraction operator.
fejerShift :
  ∀ {m k : Nat} →
  CP.FejerMonotone (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})
fejerShift {m} {k} =
  record
    { fejer = λ x y fix →
        let
          U = FAM.ultrametricVec {n = m + k}
          ne = ROSS.nonexpP {m} {k}
          step = SCC.NonExpansive.nonexp ne x y
        in
        subst (λ v → Data.Nat._≤_
                     (UMetric.Ultrametric.d U (TCP.Pᵣ {m} {k} x) v)
                     (UMetric.Ultrametric.d U x y))
              fix
              step
    }

fejer⇒closestShift :
  ∀ {m k : Nat} →
  ∀ x y →
    CP.FixP (ESB.ProjShift {m} {k}) y →
    Data.Nat._≤_
      (E.EnergySpace.E (ESB.EnergyShift {m} {k}) x (TCP.Pᵣ {m} {k} x))
      (E.EnergySpace.E (ESB.EnergyShift {m} {k}) x y)
fejer⇒closestShift {m} {k} x y fix =
  let
    U = FAM.ultrametricVec {n = m + k}
    d = UMetric.Ultrametric.d U
    tri : Data.Nat._≤_ (d x (TCP.Pᵣ {m} {k} x)) (d x y ⊔ d y (TCP.Pᵣ {m} {k} x))
    tri = UMetric.Ultrametric.ultratriangle U x y (TCP.Pᵣ {m} {k} x)
    sym1 : d y (TCP.Pᵣ {m} {k} x) ≡ d (TCP.Pᵣ {m} {k} x) y
    sym1 = UMetric.Ultrametric.symmetric U y (TCP.Pᵣ {m} {k} x)
    fejer-bound :
      Data.Nat._≤_ (d (TCP.Pᵣ {m} {k} x) y) (d x y)
    fejer-bound =
      CP.FejerMonotone.fejer (fejerShift {m} {k}) x y fix
    max-bound : Data.Nat._≤_ (d x y ⊔ d y (TCP.Pᵣ {m} {k} x)) (d x y)
    max-bound =
      NatP.⊔-lub
        (NatP.≤-refl)
        (subst (λ v → Data.Nat._≤_ v (d x y)) (sym sym1) fejer-bound)
  in
  NatP.≤-trans tri max-bound

closestAxiomsShift : CPA.ClosestPointAxiomsShift
closestAxiomsShift =
  record
    { closestAxiomShift =
        λ {m} {k} →
          record
            { fejer = fejerShift {m} {k}
            ; fejer⇒closest = fejer⇒closestShift {m} {k}
            }
    }

closestShift :
  ∀ {m k : Nat} →
  CP.ClosestPoint (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})
closestShift {m} {k} =
  FC.closestFromFejer (ESB.EnergyShift {m} {k}) (ESB.ProjShift {m} {k})
    (CPA.closestAxiomShift closestAxiomsShift {m} {k})

fejerImpliesClosestShift :
  ∀ {m k : Nat} →
  CP.FejerImpliesClosest
    (ESB.EnergyShift {m} {k})
    (ESB.ProjShift {m} {k})
    (fejerShift {m} {k})
fejerImpliesClosestShift {m} {k} =
  record
    { proof = closestShift {m} {k} }
