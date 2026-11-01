module DASHI.Geometry.RealFiniteSpeed.Instance.Shift where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Vec using (Vec)
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Geometry.RealFiniteSpeed.Core as RFS
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Physics.RealOperatorStackShift as ROSS
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
  ∀ {m k} (x y : Vec Trit (m + k)) →
  local x y →
  local (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
        (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} y)))
preservesLocality {m} {k} x y h =
  let
    open UMetric.Ultrametric (FAM.ultrametricVec {n = m + k})
    step1 : d (ROSS.P {m} {k} (ROSS.R {m} {k} x)) (ROSS.P {m} {k} (ROSS.R {m} {k} y))
            ≤ d (ROSS.R {m} {k} x) (ROSS.R {m} {k} y)
    step1 = SCC.NonExpansive.nonexp (ROSS.nonexpP {m} {k}) (ROSS.R {m} {k} x) (ROSS.R {m} {k} y)
    step2 : d (ROSS.R {m} {k} x) (ROSS.R {m} {k} y) ≤ d x y
    step2 = SCC.NonExpansive.nonexp (ROSS.nonexpR {m} {k}) x y
    step3 : d (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
               (ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} y)))
            ≤ d (ROSS.P {m} {k} (ROSS.R {m} {k} x))
               (ROSS.P {m} {k} (ROSS.R {m} {k} y))
    step3 = SCC.NonExpansive.nonexp (ROSS.nonexpC {m} {k})
              (ROSS.P {m} {k} (ROSS.R {m} {k} x))
              (ROSS.P {m} {k} (ROSS.R {m} {k} y))
  in
  NatP.≤-trans (NatP.≤-trans step3 step1) (NatP.≤-trans step2 h)

realFiniteSpeedInstance :
  ∀ {m k} →
  RFS.RealFiniteSpeed (λ x → ROSS.C {m} {k} (ROSS.P {m} {k} (ROSS.R {m} {k} x)))
realFiniteSpeedInstance {m} {k} =
  record
    { local = local {n = m + k}
    ; preservesLocality = preservesLocality {m} {k}
    }
