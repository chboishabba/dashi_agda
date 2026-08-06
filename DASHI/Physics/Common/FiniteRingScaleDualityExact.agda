module DASHI.Physics.Common.FiniteRingScaleDualityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- London Mathematical Society Student Texts 43, Cambridge University Press,
-- 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", CBMS-NSF Regional Conference Series in
-- Applied Mathematics 61, SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
--
-- Keep three notions distinct: the cardinality b of a residue fibre, the
-- spatial refinement ratio 1/b and the dual frequency expansion ratio b.
-- The exact invariant is represented without division by a cross-product
-- equality.  This is reusable for dyadic LP shells, triadic DASHI refinement
-- and scale-normalized RG bookkeeping.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_*_; _+_)

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

triadicTwoStepCocycle : MultiplicativeScaleCocycle
triadicTwoStepCocycle = multiplicativeScaleCocycle 3 3 9 refl

triadicNineAsTwoPlusSevenCocycle : MultiplicativeScaleCocycle
triadicNineAsTwoPlusSevenCocycle =
  multiplicativeScaleCocycle 9 2187 19683 refl

record RingScaleBoundary : Set where
  constructor ringScaleBoundary
  field
    largestDigitIsBaseCardinality : Set
    largestDigitIsNotBaseCardinality :
      largestDigitIsBaseCardinality → Set
    finiteDualityConstructsContinuumHarmonicAnalysis : Set
    finiteDualityDoesNotConstructContinuumHarmonicAnalysis :
      finiteDualityConstructsContinuumHarmonicAnalysis → Set

canonicalRingScaleBoundary : RingScaleBoundary
canonicalRingScaleBoundary =
  ringScaleBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
