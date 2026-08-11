module DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- State the exact producer boundary for the common Möbius basis without
-- deleting redundant constraint rows.  Both the source s=Lg and the literal
-- raw extractor defect delta=Lw are reconstructed from the same fifteen
-- nonempty subsets of the plaquette's four Wilson factors.  The Green pair
-- kernel uses the certified Moore--Penrose matrix K+.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

rawExtractorConstraintDefect :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  Physical.PhysicalSU2BondField4 → Plaquette.Plaquette4 →
  Pseudo.MultiplierVector Multiplier
rawExtractorConstraintDefect pseudoData bondField plaquette =
  Pseudo.constraintApply pseudoData
    (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)

record SelectedConstraintAtomData
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (firstVariationCovector rawExtractor : KKT.StateVector) : Set₁ where
  field
    sourceAtom : Cube.Subset4 → Multiplier → ℚ
    defectAtom : Cube.Subset4 → Multiplier → ℚ

    sourceAtomsReconstruct : ∀ row →
      Sums.sumRational Cube.nonemptySubsets4
        (λ subset → sourceAtom subset row)
      ≡ Pseudo.constraintApply pseudoData firstVariationCovector row

    defectAtomsReconstruct : ∀ row →
      Sums.sumRational Cube.nonemptySubsets4
        (λ subset → defectAtom subset row)
      ≡ Pseudo.constraintApply pseudoData rawExtractor row

open SelectedConstraintAtomData public

selectedConstraintSourceAtomsExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (atoms : SelectedConstraintAtomData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → sourceAtom atoms subset row)
  ≡ Pseudo.constraintApply pseudoData firstVariationCovector row
selectedConstraintSourceAtomsExact = sourceAtomsReconstruct

selectedRawExtractorConstraintDefectAtomsExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (atoms : SelectedConstraintAtomData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → defectAtom atoms subset row)
  ≡ Pseudo.constraintApply pseudoData rawExtractor row
selectedRawExtractorConstraintDefectAtomsExact = defectAtomsReconstruct

record LiteralRawExtractorAtomData
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (firstVariationCovector : KKT.StateVector)
    (bondField : Physical.PhysicalSU2BondField4)
    (plaquette : Plaquette.Plaquette4) : Set₁ where
  field
    atoms : SelectedConstraintAtomData
      pseudoData firstVariationCovector
      (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
open LiteralRawExtractorAtomData public

literalRawDefectAtomReconstruction :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (literal : LiteralRawExtractorAtomData
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → defectAtom (atoms literal) subset row)
  ≡ rawExtractorConstraintDefect
      pseudoData bondField plaquette row
literalRawDefectAtomReconstruction literal =
  defectAtomsReconstruct (atoms literal)

greenAtomPairValue :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (source defect : Multiplier → ℚ) →
    Multiplier → Multiplier → ℚ
greenAtomPairValue pseudoData source defect left right =
  source left
  * (Pseudo.gramPseudoinverse pseudoData left right * defect right)

selectedConstraintAtomPairKernel :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  SelectedConstraintAtomData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Cube.Subset4 → Cube.Subset4 → Multiplier → Multiplier → ℚ
selectedConstraintAtomPairKernel {pseudoData = pseudoData} atoms
    sourceSubset defectSubset =
  greenAtomPairValue pseudoData
    (sourceAtom atoms sourceSubset)
    (defectAtom atoms defectSubset)

record ConstraintAtomSupport
    {Multiplier : Set}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector rawExtractor : KKT.StateVector}
    (atoms : SelectedConstraintAtomData
      pseudoData firstVariationCovector rawExtractor)
    (collar : Multiplier → Set) : Set₁ where
  field
    sourceAtomOutsideZero : ∀ subset row →
      (collar row → ⊥) →
      sourceAtom atoms subset row ≡ 0ℚ
    defectAtomOutsideZero : ∀ subset row →
      (collar row → ⊥) →
      defectAtom atoms subset row ≡ 0ℚ
open ConstraintAtomSupport public

selectedConstraintAtomDecompositionLevel : ProofLevel
selectedConstraintAtomDecompositionLevel = machineChecked

selectedLiteralRawDefectAtomReconstructionLevel : ProofLevel
selectedLiteralRawDefectAtomReconstructionLevel = machineChecked

selectedPhysicalConstraintAtomProducerLevel : ProofLevel
selectedPhysicalConstraintAtomProducerLevel = conditional
