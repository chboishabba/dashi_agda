module DASHI.Metric.CompleteFineAgreementUltrametric where

open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ultrametric as UMetric
open import DASHI.Metric.FineAgreementUltrametric as FAM
open import DASHI.Geometry.CompleteUltrametric as CU
open import DASHI.Geometry.CompleteUltrametricNat as CUN

completeVec : ∀ {n : Nat} → CU.Complete (FAM.ultrametricVec {n})
completeVec {n} = CUN.completeNatUltrametric (FAM.ultrametricVec {n})
