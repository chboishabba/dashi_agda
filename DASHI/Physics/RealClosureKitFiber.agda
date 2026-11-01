module DASHI.Physics.RealClosureKitFiber where

open import Agda.Builtin.Equality using (_≡_)
open import Ultrametric as UMetric
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Geometry.FiberContraction as FC
open import DASHI.Combinatorics.Entropy using (Involution)
open import DASHI.Geometry.RealIsotropy.Core as RIS
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS
open import DASHI.Physics.TOperator as TOp

record RealClosureKitFiber : Set₁ where
  field
    S : Set
    U : UMetric.Ultrametric S

    C P R : S → S

    nonexpC : SCC.NonExpansive U C
    nonexpR : SCC.NonExpansive U R
    strictP-fiber : FC.ContractiveOnFibers U P
    orderLaws : SCC.OrderLaws

    -- Observable space (quotient / tail-band).
    Obs : Set
    obs : S → Obs
    obs0 : Obs
    obsT : Obs → Obs
    obsFixed : obsT obs0 ≡ obs0
    obsUnique : ∀ o → obsT o ≡ o → o ≡ obs0

    inv : Involution S
    iso : RIS.RealIsotropy U (TOp.TOperator.T (record { C = C ; P = P ; R = R }))
    fs  : RFS.RealFiniteSpeed (TOp.TOperator.T (record { C = C ; P = P ; R = R }))

open RealClosureKitFiber public
