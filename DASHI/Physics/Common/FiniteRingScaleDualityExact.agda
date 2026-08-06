module DASHI.Physics.Common.FiniteRingScaleDualityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
-- Audrey Terras, "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
-- Ingrid Daubechies, "Ten Lectures on Wavelets".
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
-- Division-free spatial/frequency reciprocal scale and multiplicative cocycle
-- algebra shared by harmonic analysis and scale-normalized RG.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_*_)

record SpatialFrequencyScale : Set where
  constructor spatialFrequencyScale
  field
    spatialNumerator : Nat
    spatialDenominator : Nat
    frequencyNumerator : Nat
    frequencyDenominator : Nat
    dualProductIsOne :
      spatialNumerator * frequencyNumerator
      ≡ spatialDenominator * frequencyDenominator

open SpatialFrequencyScale public

dyadicOneStep : SpatialFrequencyScale
dyadicOneStep = spatialFrequencyScale 1 2 2 1 refl

triadicOneStep : SpatialFrequencyScale
triadicOneStep = spatialFrequencyScale 1 3 3 1 refl

triadicNineStep : SpatialFrequencyScale
triadicNineStep = spatialFrequencyScale 1 19683 19683 1 refl

triadicNineDualityExact :
  spatialNumerator triadicNineStep * frequencyNumerator triadicNineStep
  ≡ spatialDenominator triadicNineStep * frequencyDenominator triadicNineStep
triadicNineDualityExact = dualProductIsOne triadicNineStep

record ResidueCardinalityAudit : Set where
  constructor residueCardinalityAudit
  field
    baseCardinality : Nat
    largestStandardResidue : Nat
    baseIsSuccessorOfLargestResidue :
      baseCardinality ≡ suc largestStandardResidue

open ResidueCardinalityAudit public

decimalResidueAudit : ResidueCardinalityAudit
decimalResidueAudit = residueCardinalityAudit 10 9 refl

ternaryResidueAudit : ResidueCardinalityAudit
ternaryResidueAudit = residueCardinalityAudit 3 2 refl

record MultiplicativeScaleCocycle : Set where
  constructor multiplicativeScaleCocycle
  field
    fineOverMiddle : Nat
    middleOverCoarse : Nat
    fineOverCoarse : Nat
    cocycleLaw : fineOverMiddle * middleOverCoarse ≡ fineOverCoarse

open MultiplicativeScaleCocycle public

triadicNineAsTwoPlusSevenCocycle : MultiplicativeScaleCocycle
triadicNineAsTwoPlusSevenCocycle =
  multiplicativeScaleCocycle 9 2187 19683 refl
