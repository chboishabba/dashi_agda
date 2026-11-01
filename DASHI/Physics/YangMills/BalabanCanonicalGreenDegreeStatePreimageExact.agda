module DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeStatePreimageExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964),
-- 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Lift the four canonical source and four canonical defect Möbius-degree
-- vectors back through the literal KKT constraint map.  The subset partials
-- are already source-native:
--
--       s_S     = L(P_S g),
--       delta_S = L(P_S w).
--
-- Using the exact degree-layer formulas and finite linearity, construct state
-- vectors g_d and w_d with
--
--       sourceDegreeVector_d = L g_d,
--       defectDegreeVector_d = L w_d.
--
-- This is the preimage bridge that lets the G2 Green estimate consume physical
-- state norms rather than a global norm of the singular K+.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PlaquetteSubsetProjectorExact as Subset
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as Green
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanSelectedConstraintMobiusDegreeLayerExact as ConstraintLayer
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanSelectedSourceSubsetConstraintPartialExact as Source
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical

scaleState : ℚ → KKT.StateVector → KKT.StateVector
scaleState coefficient state coordinate = coefficient * state coordinate

constraintApplyScaleExact :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    coefficient state row →
  Pseudo.constraintApply pseudoData (scaleState coefficient state) row
  ≡ coefficient * Pseudo.constraintApply pseudoData state row
constraintApplyScaleExact pseudoData coefficient state row =
  let
    coordinates = Matrix.coordinates KKT.physicalStateCarrier
    matrix = Pseudo.constraintMatrix pseudoData
  in
  trans
    (Sums.sumRationalCong coordinates _ _
      (λ coordinate → ℚRing.solve-∀
        (matrix row coordinate) coefficient (state coordinate)))
    (Sums.sumRationalScale coefficient coordinates
      (λ coordinate → matrix row coordinate * state coordinate))

sourceSubsetState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Cube.Subset4 → KKT.StateVector
sourceSubsetState {firstVariationCovector = source} {plaquette = plaquette}
    inputs subset =
  Subset.subsetBoundaryProject subset plaquette source

defectSubsetState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Cube.Subset4 → KKT.StateVector
defectSubsetState {bondField = bondField} {plaquette = plaquette}
    inputs subset =
  Subset.rawSubsetExtractor bondField plaquette subset

sourceLayerState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → KKT.StateVector
sourceLayerState inputs degree =
  Green.sumVector (Degree.degreeSubsets degree) (sourceSubsetState inputs)

defectLayerState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → KKT.StateVector
defectLayerState inputs degree =
  Green.sumVector (Degree.degreeSubsets degree) (defectSubsetState inputs)

sourceDegreeState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → KKT.StateVector
sourceDegreeState inputs Degree.degree1 = sourceLayerState inputs Degree.degree1
sourceDegreeState inputs Degree.degree2 =
  Rect.vectorSubtract
    (sourceLayerState inputs Degree.degree2)
    (scaleState (+ 3 / 1) (sourceLayerState inputs Degree.degree1))
sourceDegreeState inputs Degree.degree3 =
  Rect.vectorAdd
    (Rect.vectorSubtract
      (sourceLayerState inputs Degree.degree3)
      (scaleState (+ 2 / 1) (sourceLayerState inputs Degree.degree2)))
    (scaleState (+ 3 / 1) (sourceLayerState inputs Degree.degree1))
sourceDegreeState inputs Degree.degree4 =
  Rect.vectorAdd
    (Rect.vectorSubtract
      (sourceLayerState inputs Degree.degree4)
      (sourceLayerState inputs Degree.degree3))
    (Rect.vectorSubtract
      (sourceLayerState inputs Degree.degree2)
      (sourceLayerState inputs Degree.degree1))

defectDegreeState :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → KKT.StateVector
defectDegreeState inputs Degree.degree1 = defectLayerState inputs Degree.degree1
defectDegreeState inputs Degree.degree2 =
  Rect.vectorSubtract
    (defectLayerState inputs Degree.degree2)
    (scaleState (+ 3 / 1) (defectLayerState inputs Degree.degree1))
defectDegreeState inputs Degree.degree3 =
  Rect.vectorAdd
    (Rect.vectorSubtract
      (defectLayerState inputs Degree.degree3)
      (scaleState (+ 2 / 1) (defectLayerState inputs Degree.degree2)))
    (scaleState (+ 3 / 1) (defectLayerState inputs Degree.degree1))
defectDegreeState inputs Degree.degree4 =
  Rect.vectorAdd
    (Rect.vectorSubtract
      (defectLayerState inputs Degree.degree4)
      (defectLayerState inputs Degree.degree3))
    (Rect.vectorSubtract
      (defectLayerState inputs Degree.degree2)
      (defectLayerState inputs Degree.degree1))

partialOf :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Atoms.SelectedConstraintPartialEvaluationData
    pseudoData firstVariationCovector
    (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
partialOf inputs =
  Source.asSelectedConstraintPartialEvaluationData
    (Canonical.sourceDefectProducer inputs)

sourceLayerValue :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Degree.MobiusDegree → Multiplier → ℚ
sourceLayerValue partial Degree.degree1 = ConstraintLayer.sourceLayer1 partial
sourceLayerValue partial Degree.degree2 = ConstraintLayer.sourceLayer2 partial
sourceLayerValue partial Degree.degree3 = ConstraintLayer.sourceLayer3 partial
sourceLayerValue partial Degree.degree4 = ConstraintLayer.sourceLayer4 partial

defectLayerValue :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Degree.MobiusDegree → Multiplier → ℚ
defectLayerValue partial Degree.degree1 = ConstraintLayer.defectLayer1 partial
defectLayerValue partial Degree.degree2 = ConstraintLayer.defectLayer2 partial
defectLayerValue partial Degree.degree3 = ConstraintLayer.defectLayer3 partial
defectLayerValue partial Degree.degree4 = ConstraintLayer.defectLayer4 partial

sourceLayerConstraintAsPartial :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    degree row →
  Pseudo.constraintApply pseudoData (sourceLayerState inputs degree) row
  ≡ sourceLayerValue (partialOf inputs) degree row
sourceLayerConstraintAsPartial {pseudoData = pseudoData} inputs degree row =
  trans
    (Green.applyRectangularSumVector
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Degree.degreeSubsets degree)
      (sourceSubsetState inputs) row)
    refl

defectLayerConstraintAsPartial :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    degree row →
  Pseudo.constraintApply pseudoData (defectLayerState inputs degree) row
  ≡ defectLayerValue (partialOf inputs) degree row
defectLayerConstraintAsPartial {pseudoData = pseudoData} inputs degree row =
  trans
    (Green.applyRectangularSumVector
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Degree.degreeSubsets degree)
      (defectSubsetState inputs) row)
    refl

sourceDegreeStateConstraintExact :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    degree row →
  Pseudo.constraintApply pseudoData (sourceDegreeState inputs degree) row
  ≡ GreenDegree.sourceDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree row
sourceDegreeStateConstraintExact inputs Degree.degree1 row =
  trans (sourceLayerConstraintAsPartial inputs Degree.degree1 row) refl
sourceDegreeStateConstraintExact {pseudoData = pseudoData} inputs Degree.degree2 row =
  let l1 = sourceLayerState inputs Degree.degree1
      l2 = sourceLayerState inputs Degree.degree2
      partial = partialOf inputs
  in trans
    (Rect.applyRectangularSubtract KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData) l2 (scaleState (+ 3 / 1) l1) row)
    (trans
      (cong (Pseudo.constraintApply pseudoData l2 row -_)
        (constraintApplyScaleExact pseudoData (+ 3 / 1) l1 row))
      (trans
        (cong₂ _-_
          (sourceLayerConstraintAsPartial inputs Degree.degree2 row)
          (cong ((+ 3 / 1) *_)
            (sourceLayerConstraintAsPartial inputs Degree.degree1 row)))
        (sym (ConstraintLayer.sourceDegree2LayerExact partial row))))
sourceDegreeStateConstraintExact {pseudoData = pseudoData} inputs Degree.degree3 row =
  let l1 = sourceLayerState inputs Degree.degree1
      l2 = sourceLayerState inputs Degree.degree2
      l3 = sourceLayerState inputs Degree.degree3
      partial = partialOf inputs
      first = Rect.vectorSubtract l3 (scaleState (+ 2 / 1) l2)
      second = scaleState (+ 3 / 1) l1
  in trans
    (Rect.applyRectangularAdd KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData) first second row)
    (trans
      (cong₂ _+_
        (trans
          (Rect.applyRectangularSubtract KKT.physicalStateCarrier
            (Pseudo.constraintMatrix pseudoData) l3
            (scaleState (+ 2 / 1) l2) row)
          (cong (Pseudo.constraintApply pseudoData l3 row -_)
            (constraintApplyScaleExact pseudoData (+ 2 / 1) l2 row)))
        (constraintApplyScaleExact pseudoData (+ 3 / 1) l1 row))
      (trans
        (cong₂ _+_
          (cong₂ _-_
            (sourceLayerConstraintAsPartial inputs Degree.degree3 row)
            (cong ((+ 2 / 1) *_)
              (sourceLayerConstraintAsPartial inputs Degree.degree2 row)))
          (cong ((+ 3 / 1) *_)
            (sourceLayerConstraintAsPartial inputs Degree.degree1 row)))
        (sym (ConstraintLayer.sourceDegree3LayerExact partial row))))
sourceDegreeStateConstraintExact {pseudoData = pseudoData} inputs Degree.degree4 row =
  let l1 = sourceLayerState inputs Degree.degree1
      l2 = sourceLayerState inputs Degree.degree2
      l3 = sourceLayerState inputs Degree.degree3
      l4 = sourceLayerState inputs Degree.degree4
      partial = partialOf inputs
  in trans
    (Rect.applyRectangularAdd KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Rect.vectorSubtract l4 l3) (Rect.vectorSubtract l2 l1) row)
    (trans
      (cong₂ _+_
        (Rect.applyRectangularSubtract KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l4 l3 row)
        (Rect.applyRectangularSubtract KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l2 l1 row))
      (trans
        (cong₂ _+_
          (cong₂ _-_
            (sourceLayerConstraintAsPartial inputs Degree.degree4 row)
            (sourceLayerConstraintAsPartial inputs Degree.degree3 row))
          (cong₂ _-_
            (sourceLayerConstraintAsPartial inputs Degree.degree2 row)
            (sourceLayerConstraintAsPartial inputs Degree.degree1 row)))
        (sym (ConstraintLayer.sourceDegree4LayerExact partial row))))

defectDegreeStateConstraintExact :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    degree row →
  Pseudo.constraintApply pseudoData (defectDegreeState inputs degree) row
  ≡ GreenDegree.defectDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree row
defectDegreeStateConstraintExact inputs Degree.degree1 row =
  trans (defectLayerConstraintAsPartial inputs Degree.degree1 row) refl
defectDegreeStateConstraintExact {pseudoData = pseudoData} inputs Degree.degree2 row =
  let l1 = defectLayerState inputs Degree.degree1
      l2 = defectLayerState inputs Degree.degree2
      partial = partialOf inputs
  in trans
    (Rect.applyRectangularSubtract KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData) l2 (scaleState (+ 3 / 1) l1) row)
    (trans
      (cong (Pseudo.constraintApply pseudoData l2 row -_)
        (constraintApplyScaleExact pseudoData (+ 3 / 1) l1 row))
      (trans
        (cong₂ _-_
          (defectLayerConstraintAsPartial inputs Degree.degree2 row)
          (cong ((+ 3 / 1) *_)
            (defectLayerConstraintAsPartial inputs Degree.degree1 row)))
        (sym (ConstraintLayer.defectDegree2LayerExact partial row))))
defectDegreeStateConstraintExact {pseudoData = pseudoData} inputs Degree.degree3 row =
  let l1 = defectLayerState inputs Degree.degree1
      l2 = defectLayerState inputs Degree.degree2
      l3 = defectLayerState inputs Degree.degree3
      partial = partialOf inputs
      first = Rect.vectorSubtract l3 (scaleState (+ 2 / 1) l2)
      second = scaleState (+ 3 / 1) l1
  in trans
    (Rect.applyRectangularAdd KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData) first second row)
    (trans
      (cong₂ _+_
        (trans
          (Rect.applyRectangularSubtract KKT.physicalStateCarrier
            (Pseudo.constraintMatrix pseudoData) l3
            (scaleState (+ 2 / 1) l2) row)
          (cong (Pseudo.constraintApply pseudoData l3 row -_)
            (constraintApplyScaleExact pseudoData (+ 2 / 1) l2 row)))
        (constraintApplyScaleExact pseudoData (+ 3 / 1) l1 row))
      (trans
        (cong₂ _+_
          (cong₂ _-_
            (defectLayerConstraintAsPartial inputs Degree.degree3 row)
            (cong ((+ 2 / 1) *_)
              (defectLayerConstraintAsPartial inputs Degree.degree2 row)))
          (cong ((+ 3 / 1) *_)
            (defectLayerConstraintAsPartial inputs Degree.degree1 row)))
        (sym (ConstraintLayer.defectDegree3LayerExact partial row))))
defectDegreeStateConstraintExact {pseudoData = pseudoData} inputs Degree.degree4 row =
  let l1 = defectLayerState inputs Degree.degree1
      l2 = defectLayerState inputs Degree.degree2
      l3 = defectLayerState inputs Degree.degree3
      l4 = defectLayerState inputs Degree.degree4
      partial = partialOf inputs
  in trans
    (Rect.applyRectangularAdd KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      (Rect.vectorSubtract l4 l3) (Rect.vectorSubtract l2 l1) row)
    (trans
      (cong₂ _+_
        (Rect.applyRectangularSubtract KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l4 l3 row)
        (Rect.applyRectangularSubtract KKT.physicalStateCarrier
          (Pseudo.constraintMatrix pseudoData) l2 l1 row))
      (trans
        (cong₂ _+_
          (cong₂ _-_
            (defectLayerConstraintAsPartial inputs Degree.degree4 row)
            (defectLayerConstraintAsPartial inputs Degree.degree3 row))
          (cong₂ _-_
            (defectLayerConstraintAsPartial inputs Degree.degree2 row)
            (defectLayerConstraintAsPartial inputs Degree.degree1 row)))
        (sym (ConstraintLayer.defectDegree4LayerExact partial row))))

canonicalSourceDegreeStatePreimageLevel : ProofLevel
canonicalSourceDegreeStatePreimageLevel = machineChecked

canonicalDefectDegreeStatePreimageLevel : ProofLevel
canonicalDefectDegreeStatePreimageLevel = machineChecked
