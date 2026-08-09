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
-- DASHI CONTRIBUTION
--
-- State the exact producer boundary for the common Möbius basis.  Both the
-- constraint source s=Lg and the literal raw extractor defect delta=Lw are
-- reconstructed from the same fifteen nonempty subsets of the plaquette's
-- four Wilson factors.  The theorem is vector-valued row by row; it does not
-- replace the source or defect by scalar receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectExact as Raw
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

record SelectedConstraintAtomData
    {Multiplier : Set}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    (firstVariationCovector rawExtractor : KKT.StateVector) : Set₁ where
  field
    sourceAtom : Cube.Subset4 → Multiplier → ℚ
    defectAtom : Cube.Subset4 → Multiplier → ℚ

    sourceAtomsReconstruct : ∀ row →
      Sums.sumRational Cube.nonemptySubsets4
        (λ subset → sourceAtom subset row)
      ≡ KKT.constraintApply projectorData firstVariationCovector row

    defectAtomsReconstruct : ∀ row →
      Sums.sumRational Cube.nonemptySubsets4
        (λ subset → defectAtom subset row)
      ≡ KKT.constraintApply projectorData rawExtractor row

open SelectedConstraintAtomData public

selectedConstraintSourceAtomsExact :
  ∀ {Multiplier projectorData firstVariationCovector rawExtractor}
    (atoms : SelectedConstraintAtomData
      {Multiplier} projectorData firstVariationCovector rawExtractor)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → sourceAtom atoms subset row)
  ≡ KKT.constraintApply projectorData firstVariationCovector row
selectedConstraintSourceAtomsExact = sourceAtomsReconstruct

selectedRawExtractorConstraintDefectAtomsExact :
  ∀ {Multiplier projectorData firstVariationCovector rawExtractor}
    (atoms : SelectedConstraintAtomData
      {Multiplier} projectorData firstVariationCovector rawExtractor)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → defectAtom atoms subset row)
  ≡ KKT.constraintApply projectorData rawExtractor row
selectedRawExtractorConstraintDefectAtomsExact = defectAtomsReconstruct

record LiteralRawExtractorAtomData
    {Multiplier : Set}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    (firstVariationCovector : KKT.StateVector)
    (bondField : Physical.PhysicalSU2BondField4)
    (plaquette : Plaquette.Plaquette4) : Set₁ where
  field
    atoms : SelectedConstraintAtomData
      projectorData firstVariationCovector
      (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
open LiteralRawExtractorAtomData public

literalRawDefectAtomReconstruction :
  ∀ {Multiplier projectorData firstVariationCovector bondField plaquette}
    (literal : LiteralRawExtractorAtomData
      {Multiplier} projectorData firstVariationCovector bondField plaquette)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → defectAtom (atoms literal) subset row)
  ≡ Raw.rawExtractorConstraintDefect
      projectorData bondField plaquette row
literalRawDefectAtomReconstruction literal =
  defectAtomsReconstruct (atoms literal)

greenAtomPairValue :
  ∀ {Multiplier}
    (projectorData : KKT.FiniteKKTProjectorData Multiplier)
    (source defect : Multiplier → ℚ) →
    Multiplier → Multiplier → ℚ
greenAtomPairValue projectorData source defect left right =
  source left
  * (KKT.multiplierGreen projectorData left right * defect right)

selectedConstraintAtomPairKernel :
  ∀ {Multiplier projectorData firstVariationCovector rawExtractor} →
  SelectedConstraintAtomData
    {Multiplier} projectorData firstVariationCovector rawExtractor →
  Cube.Subset4 → Cube.Subset4 → Multiplier → Multiplier → ℚ
selectedConstraintAtomPairKernel {projectorData = projectorData} atoms
    sourceSubset defectSubset =
  greenAtomPairValue projectorData
    (sourceAtom atoms sourceSubset)
    (defectAtom atoms defectSubset)

record ConstraintAtomSupport
    {Multiplier : Set}
    {projectorData : KKT.FiniteKKTProjectorData Multiplier}
    {firstVariationCovector rawExtractor : KKT.StateVector}
    (atoms : SelectedConstraintAtomData
      projectorData firstVariationCovector rawExtractor)
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
