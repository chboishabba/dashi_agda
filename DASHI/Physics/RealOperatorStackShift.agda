module DASHI.Physics.RealOperatorStackShift where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.CanonicalizationMinimal as CM
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Metric.AgreementUltrametric as AM
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Geometry.FiberContraction as FC
open import Ultrametric as UMetric
open import Contraction using (_≢_)
open import Relation.Binary.PropositionalEquality using (sym; subst; trans; cong; subst₂)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Properties as NatP
open import Data.Vec.Base using (reverse; _++_)
open import Data.Product using (_,_)

C : ∀ {m k : Nat} → RTC.Carrier (m + k) → RTC.Carrier (m + k)
C {m} {k} = CM.Cᵣ {m} {k}

P : ∀ {m k : Nat} → RTC.Carrier (m + k) → RTC.Carrier (m + k)
P {m} {k} = TCP.Pᵣ {m} {k}

R : ∀ {m k : Nat} → RTC.Carrier (m + k) → RTC.Carrier (m + k)
R {m} {k} = TCP.Rᵣ {m} {k}

nonexpC : ∀ {m k : Nat} → SCC.NonExpansive (FAM.ultrametricVec {n = m + k}) (C {m} {k})
nonexpC {m} {k} = CM.nonexpCᵣ {m} {k}

nonexpR : ∀ {m k : Nat} → SCC.NonExpansive (FAM.ultrametricVec {n = m + k}) (R {m} {k})
nonexpR {m} {k} =
  record
    { nonexp = nonexp }
  where
    nonexp : ∀ x y → UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) (R {m} {k} x) (R {m} {k} y)
                       ≤ UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y
    nonexp x y =
      let
        cx = TCP.coarseOf m k x
        tx = TCP.tailOf m k x
        cy = TCP.coarseOf m k y
        ty = TCP.tailOf m k y
        p : x ≡ cx ++ tx
        p = sym (TCP.merge-split m k x)
        q : y ≡ cy ++ ty
        q = sym (TCP.merge-split m k y)
        r : R {m} {k} x ≡ cx ++ TCP.shiftTail tx
        r = trans (cong (λ v → R {m} {k} v) p) (TCP.Rᵣ-++ m k cx tx)
        s : R {m} {k} y ≡ cy ++ TCP.shiftTail ty
        s = trans (cong (λ v → R {m} {k} v) q) (TCP.Rᵣ-++ m k cy ty)
        step : FAM.dNatFine (cx ++ TCP.shiftTail tx) (cy ++ TCP.shiftTail ty)
               ≤ FAM.dNatFine (cx ++ tx) (cy ++ ty)
        step = FAM.dNatFine-++-shiftTail≤ cx cy tx ty
        step1 : FAM.dNatFine (R {m} {k} x) (R {m} {k} y)
                 ≤ FAM.dNatFine (cx ++ tx) (cy ++ ty)
        step1 =
          subst₂
            (λ a b → FAM.dNatFine a b ≤ FAM.dNatFine (cx ++ tx) (cy ++ ty))
            (sym r) (sym s) step
        step2 : FAM.dNatFine (cx ++ tx) (cy ++ ty) ≡ FAM.dNatFine x y
        step2 = subst₂
          (λ x' y' → FAM.dNatFine (cx ++ tx) (cy ++ ty) ≡ FAM.dNatFine x' y')
          (sym p) (sym q) refl
      in
      NatP.≤-trans step1 (NatP.≤-reflexive step2)

nonexpP : ∀ {m k : Nat} → SCC.NonExpansive (FAM.ultrametricVec {n = m + k}) (P {m} {k})
nonexpP {m} {k} =
  record
    { nonexp = nonexp }
  where
    nonexp : ∀ x y →
      UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) (P {m} {k} x) (P {m} {k} y)
        ≤ UMetric.Ultrametric.d (FAM.ultrametricVec {n = m + k}) x y
    nonexp x y =
      let
        cx = TCP.coarseOf m k x
        tx = TCP.tailOf m k x
        cy = TCP.coarseOf m k y
        ty = TCP.tailOf m k y
        p : x ≡ cx ++ tx
        p = sym (TCP.merge-split m k x)
        q : y ≡ cy ++ ty
        q = sym (TCP.merge-split m k y)
        r : P {m} {k} x ≡ cx ++ TCP.projTail tx
        r = trans (cong (λ v → P {m} {k} v) p) (TCP.Pᵣ-++ m k cx tx)
        s : P {m} {k} y ≡ cy ++ TCP.projTail ty
        s = trans (cong (λ v → P {m} {k} v) q) (TCP.Pᵣ-++ m k cy ty)
        step : FAM.dNatFine (cx ++ TCP.projTail tx) (cy ++ TCP.projTail ty)
               ≤ FAM.dNatFine (cx ++ tx) (cy ++ ty)
        step = FAM.dNatFine-++-projTail≤ cx cy tx ty
        step1 : FAM.dNatFine (P {m} {k} x) (P {m} {k} y)
                 ≤ FAM.dNatFine (cx ++ tx) (cy ++ ty)
        step1 =
          subst₂
            (λ a b → FAM.dNatFine a b ≤ FAM.dNatFine (cx ++ tx) (cy ++ ty))
            (sym r) (sym s) step
        step2 : FAM.dNatFine (cx ++ tx) (cy ++ ty) ≡ FAM.dNatFine x y
        step2 = subst₂
          (λ x' y' → FAM.dNatFine (cx ++ tx) (cy ++ ty) ≡ FAM.dNatFine x' y')
          (sym p) (sym q) refl
      in
      NatP.≤-trans step1 (NatP.≤-reflexive step2)

strictP-fiber :
  ∀ {m k : Nat} →
  FC.ContractiveOnFibers (FAM.ultrametricVec {n = m + k}) (P {m} {k})
strictP-fiber {m} {k} =
  record
    { contractFiber = λ {x} {y} fd →
        let
          open UMetric.Ultrametric (FAM.ultrametricVec {n = m + k})
          open FC.FiberDistinct fd using (x≢y; sameFiber)
          d0 : d (P {m} {k} x) (P {m} {k} y) ≡ 0
          d0 = subst (λ z → d (P {m} {k} x) z ≡ 0) sameFiber (id-zero (P {m} {k} x))
        in
        subst (λ u → u < d x y) (sym d0) (FAM.dNatFine-positive x≢y)
    }
