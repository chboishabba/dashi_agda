module DASHI.Physics.RealOperatorStack where

open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealOperators as RO
open import Contraction
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Geometry.FiberContraction as FC
open import Ultrametric as UMetric
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Data.Nat using (_<_)
open import Agda.Builtin.Equality using (_≡_)

C P R : ∀ {n} → RTC.Carrier n → RTC.Carrier n
C {n} = RO.Cᵣ {n}
P {n} = RO.Pᵣ {n}
R {n} = RO.Rᵣ {n}

nonexpC : ∀ {n} → SCC.NonExpansive (FAM.ultrametricVec {n = n}) (C {n})
nonexpC {n} = RO.nonexpCᵣ {n}

nonexpR : ∀ {n} → SCC.NonExpansive (FAM.ultrametricVec {n = n}) (R {n})
nonexpR {n} = RO.nonexpRᵣ {n}

strictP-fiber : ∀ {n} → FC.ContractiveOnFibers (FAM.ultrametricVec {n = n}) (P {n})
strictP-fiber {n} =
  record
    { contractFiber = λ {x} {y} fd →
        let
          open UMetric.Ultrametric (FAM.ultrametricVec {n = n})
          open FC.FiberDistinct fd using (x≢y; sameFiber)
          d0 : d (P x) (P y) ≡ 0
          d0 = subst (λ z → d (P x) z ≡ 0) sameFiber (id-zero (P x))
        in
        subst (λ k → k < d x y) (sym d0) (FAM.dNatFine-positive x≢y)
    }
