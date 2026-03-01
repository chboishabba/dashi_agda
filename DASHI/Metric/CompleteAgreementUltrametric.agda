module DASHI.Metric.CompleteAgreementUltrametric where

open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ultrametric as UMetric
open import DASHI.Metric.AgreementUltrametric as AM
open import DASHI.Geometry.CompleteUltrametric as CU
open import DASHI.Geometry.CompleteUltrametricNat as CUN

completeVec : ∀ {n : Nat} → CU.Complete (AM.ultrametricVec {n})
completeVec {n} = CUN.completeNatUltrametric (AM.ultrametricVec {n})
