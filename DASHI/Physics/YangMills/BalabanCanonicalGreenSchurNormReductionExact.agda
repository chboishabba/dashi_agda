module DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Issai Schur, classical matrix norm test (1911).  No DOI applies to the
-- original result.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Specialize the square-root-free Schur energy theorem to the SAME four
-- canonical source and four canonical defect degree vectors used by G2.
-- Once one common row-mass bound B for K+ is known, any vector norm endpoint
-- V produces the diagonal-energy endpoint
--
--   E(B,V) = (1/2)(1+B^2)V.
--
-- The Round60 polarization/endpoint compiler then generates the complete 4x4
-- signed Green table.  No separate K+ action bounds are required per pair.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _*_; _/_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as DegreeGreen
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact as Diagonal
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact as Energy
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree

half : ℚ
half = + 1 / 2

canonicalSourceDegreeNormSq :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) →
  Degree.MobiusDegree → ℚ
canonicalSourceDegreeNormSq {pseudoData = pseudoData} inputs degree =
  Schur.vectorNormSq
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (DegreeGreen.sourceDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree)

canonicalDefectDegreeNormSq :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) →
  Degree.MobiusDegree → ℚ
canonicalDefectDegreeNormSq {pseudoData = pseudoData} inputs degree =
  Schur.vectorNormSq
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (DegreeGreen.defectDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree)

derivedEnergyUpper :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier} →
  Energy.PseudoinverseSchurBound pseudoData → ℚ → ℚ
derivedEnergyUpper schur vectorNormUpper =
  half *
    ((1ℚ + Energy.rowMassBound schur * Energy.rowMassBound schur)
      * vectorNormUpper)

canonicalSourceEnergyUpperFromNorm :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (schur : Energy.PseudoinverseSchurBound pseudoData)
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    degree vectorNormUpper →
  canonicalSourceDegreeNormSq inputs degree ≤ vectorNormUpper →
  Diagonal.canonicalSourceDegreeEnergy inputs degree
  ≤ derivedEnergyUpper schur vectorNormUpper
canonicalSourceEnergyUpperFromNorm
    {pseudoData = pseudoData} schur inputs degree vectorNormUpper normBound =
  Energy.pseudoEnergyUpperFromVectorNorm
    schur
    (DegreeGreen.sourceDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree)
    vectorNormUpper normBound

canonicalDefectEnergyUpperFromNorm :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (schur : Energy.PseudoinverseSchurBound pseudoData)
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    degree vectorNormUpper →
  canonicalDefectDegreeNormSq inputs degree ≤ vectorNormUpper →
  Diagonal.canonicalDefectDegreeEnergy inputs degree
  ≤ derivedEnergyUpper schur vectorNormUpper
canonicalDefectEnergyUpperFromNorm
    {pseudoData = pseudoData} schur inputs degree vectorNormUpper normBound =
  Energy.pseudoEnergyUpperFromVectorNorm
    schur
    (DegreeGreen.defectDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree)
    vectorNormUpper normBound

canonicalGreenSchurNormReductionLevel : ProofLevel
canonicalGreenSchurNormReductionLevel = machineChecked

-- Remaining A2 quantitative input after this specialization:
--   one common absolute-row-mass bound for K+;
--   four source-degree norm-square endpoints;
--   four defect-degree norm-square endpoints.
selectedRegionOneSchurPlusEightNormBoundsLevel : ProofLevel
selectedRegionOneSchurPlusEightNormBoundsLevel = conditional
