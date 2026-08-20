module DASHI.Physics.YangMills.BalabanSelectedSourceSubsetConstraintPartialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories", Communications in
-- Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Roger Penrose, "A Generalized Inverse for Matrices", Proceedings of the
-- Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Gian-Carlo Rota, "On the Foundations of Combinatorial Theory I. Theory of
-- Möbius Functions", Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964),
-- 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
-- Round56 already constructed the sixteen DEFECT partials
--
--       delta_S = L(P_S w).
--
-- The source half previously remained an arbitrary sixteen-value family.  For
-- a literal single-plaquette source covector g whose support lies in the four
-- boundary bonds, use THE SAME projectors:
--
--       s_S = L(P_S g).
--
-- Empty is zero by the concrete diagonal projector; full is Lg because the
-- boundary projector fixes any vector in its image.  Therefore the entire
-- source/defect Möbius family is generated from one physical support theorem,
-- not sixteen independent source evaluations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PlaquetteSubsetProjectorExact as Subset
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorSubsetDefectPartialExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms

record PlaquetteSupportedSource
    (plaquette : Plaquette.Plaquette4)
    (source : KKT.StateVector) : Set₁ where
  field
    support :
      Projector.PhysicalConstraintProjectorImage
        (Boundary.plaquetteBoundaryMask plaquette) source
open PlaquetteSupportedSource public

boundaryProjectFixesSupportedSource :
  ∀ {plaquette source} →
  PlaquetteSupportedSource plaquette source →
  ∀ coordinate →
  Boundary.plaquetteBoundaryProject plaquette source coordinate
  ≡ source coordinate
boundaryProjectFixesSupportedSource supported =
  Projector.physicalConstraintProjectorImageCharacterizationForward
    _ _ (support supported)

sourceSubsetConstraint :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier →
  Plaquette.Plaquette4 → KKT.StateVector →
  Cube.Subset4 → Multiplier → ℚ
sourceSubsetConstraint pseudoData plaquette source subset =
  Pseudo.constraintApply pseudoData
    (Subset.subsetBoundaryProject subset plaquette source)

sourceSubsetConstraintEmptyZero :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    plaquette source row →
  sourceSubsetConstraint pseudoData plaquette source Cube.empty row ≡ 0ℚ
sourceSubsetConstraintEmptyZero pseudoData plaquette source row =
  trans
    (Rect.applyRectangularVectorCong
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Subset.emptySubsetProjectZero plaquette source)
      row)
    (Rect.applyRectangularZero
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      row)

sourceSubsetConstraintFullExact :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    plaquette source →
  PlaquetteSupportedSource plaquette source →
  ∀ row →
  sourceSubsetConstraint pseudoData plaquette source Cube.s0123 row
  ≡ Pseudo.constraintApply pseudoData source row
sourceSubsetConstraintFullExact pseudoData plaquette source supported row =
  let
    fullToBoundary : ∀ coordinate →
      Subset.subsetBoundaryProject Cube.s0123 plaquette source coordinate
      ≡ Boundary.plaquetteBoundaryProject plaquette source coordinate
    fullToBoundary = Subset.fullSubsetProjectIsBoundaryProject plaquette source

    fullToSource : ∀ coordinate →
      Subset.subsetBoundaryProject Cube.s0123 plaquette source coordinate
      ≡ source coordinate
    fullToSource coordinate =
      trans (fullToBoundary coordinate)
        (boundaryProjectFixesSupportedSource supported coordinate)
  in
  Rect.applyRectangularVectorCong
    KKT.physicalStateCarrier
    (Pseudo.constraintMatrix pseudoData)
    fullToSource row

record LiteralSourceDefectSubsetProducer
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (firstVariationCovector : KKT.StateVector)
    (bondField : Physical.PhysicalSU2BondField4)
    (plaquette : Plaquette.Plaquette4) : Set₁ where
  field
    sourceSupported :
      PlaquetteSupportedSource plaquette firstVariationCovector
open LiteralSourceDefectSubsetProducer public

asSelectedConstraintPartialEvaluationData :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  LiteralSourceDefectSubsetProducer
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Atoms.SelectedConstraintPartialEvaluationData
    pseudoData firstVariationCovector
    (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
asSelectedConstraintPartialEvaluationData
    {pseudoData = pseudoData}
    {firstVariationCovector = source}
    {bondField = bondField}
    {plaquette = plaquette}
    producer = record
  { Atoms.SelectedConstraintPartialEvaluationData.sourcePartial =
      sourceSubsetConstraint pseudoData plaquette source
  ; Atoms.SelectedConstraintPartialEvaluationData.defectPartial =
      Defect.rawSubsetConstraintDefect pseudoData bondField plaquette
  ; Atoms.SelectedConstraintPartialEvaluationData.sourceEmptyZero =
      sourceSubsetConstraintEmptyZero pseudoData plaquette source
  ; Atoms.SelectedConstraintPartialEvaluationData.defectEmptyZero =
      Defect.rawSubsetConstraintDefectEmptyZero pseudoData bondField plaquette
  ; Atoms.SelectedConstraintPartialEvaluationData.sourceFullExact =
      sourceSubsetConstraintFullExact pseudoData plaquette source
        (sourceSupported producer)
  ; Atoms.SelectedConstraintPartialEvaluationData.defectFullExact =
      Defect.rawSubsetConstraintDefectFullExact pseudoData bondField plaquette
  }

literalSourceDefectMobiusAtoms :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  LiteralSourceDefectSubsetProducer
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Atoms.SelectedConstraintAtomData
    pseudoData firstVariationCovector
    (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
literalSourceDefectMobiusAtoms producer =
  Atoms.atomsFromPartialEvaluations
    (asSelectedConstraintPartialEvaluationData producer)

sourceSixteenSubsetConstructionLevel : ProofLevel
sourceSixteenSubsetConstructionLevel = machineChecked

sourceDefectMobiusProducerFromSingleSupportLevel : ProofLevel
sourceDefectMobiusProducerFromSingleSupportLevel = machineChecked

-- The G2 source-partial frontier is now ONE physical theorem: the selected
-- single-plaquette first-variation covector is supported on the four boundary
-- bonds.  The sixteen source values, sixteen defect values, Möbius transform and
-- KKT endpoint identities are all generated once that support is established.
selectedPhysicalFirstVariationPlaquetteSupportLevel : ProofLevel
selectedPhysicalFirstVariationPlaquetteSupportLevel = conditional
