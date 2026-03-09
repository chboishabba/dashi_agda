module DASHI.Geometry.RealFiniteSpeed.Instance.Core where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec)
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealOperators as RO
open import Ultrametric as UMetric
open import DASHI.Geometry.StrictContractionComposition as SCC
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP

-- Fixed locality radius (nontrivial, but simple).
radius : Nat
radius = suc zero

local : ∀ {n} → (x y : Vec Trit n) → Set
local {n} x y = UMetric.Ultrametric.d (FAM.ultrametricVec {n = n}) x y ≤ radius

preservesLocality :
  ∀ {n} (x y : Vec Trit n) →
  local x y →
  local (RO.Cᵣ (RO.Pᵣ (RO.Rᵣ x))) (RO.Cᵣ (RO.Pᵣ (RO.Rᵣ y)))
preservesLocality {n} x y h =
  let
    open UMetric.Ultrametric (FAM.ultrametricVec {n = n})
    step1 : d (RO.Pᵣ (RO.Rᵣ x)) (RO.Pᵣ (RO.Rᵣ y)) ≤ d (RO.Rᵣ x) (RO.Rᵣ y)
    step1 = SCC.NonExpansive.nonexp (RO.nonexpPᵣ {n}) (RO.Rᵣ x) (RO.Rᵣ y)
    step2 : d (RO.Rᵣ x) (RO.Rᵣ y) ≤ d x y
    step2 = SCC.NonExpansive.nonexp (RO.nonexpRᵣ {n}) x y
    step3 : d (RO.Cᵣ (RO.Pᵣ (RO.Rᵣ x))) (RO.Cᵣ (RO.Pᵣ (RO.Rᵣ y)))
            ≤ d (RO.Pᵣ (RO.Rᵣ x)) (RO.Pᵣ (RO.Rᵣ y))
    step3 = SCC.NonExpansive.nonexp (RO.nonexpCᵣ {n}) (RO.Pᵣ (RO.Rᵣ x)) (RO.Pᵣ (RO.Rᵣ y))
  in
  NatP.≤-trans (NatP.≤-trans step3 step1) (NatP.≤-trans step2 h)

realFiniteSpeedInstance :
  ∀ {n} →
  RFS.RealFiniteSpeed (λ x → RO.Cᵣ (RO.Pᵣ (RO.Rᵣ x)))
realFiniteSpeedInstance {n} =
  record
    { local = local {n}
    ; preservesLocality = preservesLocality {n}
    }
