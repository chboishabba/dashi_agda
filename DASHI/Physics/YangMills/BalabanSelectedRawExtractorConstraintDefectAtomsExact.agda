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
-- Put the source s=Lg and literal raw-extractor defect delta=Lw in the SAME
-- canonical Boolean-four-cube Möbius basis without deleting redundant
-- constraint rows.  Earlier code allowed callers to supply arbitrary fifteen
-- atoms together with reconstruction equalities.  This file now also provides
-- the stronger producer-shaped route:
--
--   literal subset evaluations on all 16 factor placements
--     -> canonical Möbius transform
--     -> 15 nonempty atoms
--     -> exact source/defect reconstruction.
--
-- Thus the combinatorial decomposition itself is no longer a physical input.
-- The remaining source-facing obligation is to construct the actual partial
-- subset evaluations and identify the empty/full placements with background
-- zero and the literal full source/defect respectively.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusExact as Mobius

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

------------------------------------------------------------------------
-- Canonical producer from literal subset evaluations.
------------------------------------------------------------------------

record SelectedConstraintPartialEvaluationData
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (firstVariationCovector rawExtractor : KKT.StateVector) : Set₁ where
  field
    sourcePartial : Cube.Subset4 → Multiplier → ℚ
    defectPartial : Cube.Subset4 → Multiplier → ℚ

    sourceEmptyZero : ∀ row → sourcePartial Cube.empty row ≡ 0ℚ
    defectEmptyZero : ∀ row → defectPartial Cube.empty row ≡ 0ℚ

    sourceFullExact : ∀ row →
      sourcePartial Cube.s0123 row
      ≡ Pseudo.constraintApply pseudoData firstVariationCovector row

    defectFullExact : ∀ row →
      defectPartial Cube.s0123 row
      ≡ Pseudo.constraintApply pseudoData rawExtractor row

open SelectedConstraintPartialEvaluationData public

sourceMobiusAtom :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Cube.Subset4 → Multiplier → ℚ
sourceMobiusAtom partial subset row =
  Mobius.mobiusAtom (λ selected → sourcePartial partial selected row) subset

defectMobiusAtom :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Cube.Subset4 → Multiplier → ℚ
defectMobiusAtom partial subset row =
  Mobius.mobiusAtom (λ selected → defectPartial partial selected row) subset

sourceMobiusAtomsReconstruct :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → sourceMobiusAtom partial subset row)
  ≡ Pseudo.constraintApply pseudoData firstVariationCovector row
sourceMobiusAtomsReconstruct partial row =
  trans
    (Mobius.nonemptyMobiusSumWithZeroBackground
      (λ selected → sourcePartial partial selected row)
      (sourceEmptyZero partial row))
    (sourceFullExact partial row)

defectMobiusAtomsReconstruct :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → defectMobiusAtom partial subset row)
  ≡ Pseudo.constraintApply pseudoData rawExtractor row
defectMobiusAtomsReconstruct partial row =
  trans
    (Mobius.nonemptyMobiusSumWithZeroBackground
      (λ selected → defectPartial partial selected row)
      (defectEmptyZero partial row))
    (defectFullExact partial row)

atomsFromPartialEvaluations :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  SelectedConstraintAtomData
    {Multiplier} pseudoData firstVariationCovector rawExtractor
atomsFromPartialEvaluations partial = record
  { sourceAtom = sourceMobiusAtom partial
  ; defectAtom = defectMobiusAtom partial
  ; sourceAtomsReconstruct = sourceMobiusAtomsReconstruct partial
  ; defectAtomsReconstruct = defectMobiusAtomsReconstruct partial
  }

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

record LiteralRawExtractorPartialEvaluationData
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (firstVariationCovector : KKT.StateVector)
    (bondField : Physical.PhysicalSU2BondField4)
    (plaquette : Plaquette.Plaquette4) : Set₁ where
  field
    partial : SelectedConstraintPartialEvaluationData
      pseudoData firstVariationCovector
      (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)

open LiteralRawExtractorPartialEvaluationData public

literalAtomsFromPartialEvaluations :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  LiteralRawExtractorPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  SelectedConstraintAtomData
    pseudoData firstVariationCovector
    (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
literalAtomsFromPartialEvaluations literal =
  atomsFromPartialEvaluations (partial literal)

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

selectedConstraintMobiusAtomConstructionLevel : ProofLevel
selectedConstraintMobiusAtomConstructionLevel = machineChecked

selectedLiteralRawDefectAtomReconstructionLevel : ProofLevel
selectedLiteralRawDefectAtomReconstructionLevel = machineChecked

-- The physical producer is now narrowed to the actual partial-subset source
-- and raw-extractor evaluations (plus support/locality). The 15-atom Möbius
-- decomposition and its reconstruction are no longer conditional inputs.
selectedPhysicalConstraintPartialEvaluationProducerLevel : ProofLevel
selectedPhysicalConstraintPartialEvaluationProducerLevel = conditional
