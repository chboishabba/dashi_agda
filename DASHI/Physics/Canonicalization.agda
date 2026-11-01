module DASHI.Physics.Canonicalization where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Geometry.StrictContractionComposition as SCC
open import DASHI.Metric.FineAgreementUltrametric as FAM

-- Placeholder interface for nontrivial canonicalization on the coarse core.
record Canonicalization (n : Nat) : Set₁ where
  field
    Cᵣ : RTC.Carrier n → RTC.Carrier n
    nonexpCᵣ : SCC.NonExpansive (FAM.ultrametricVec {n = n}) Cᵣ
