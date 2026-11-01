module DASHI.Physics.YangMills.BalabanSelectedConstraintMobiusDegreeLayerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Apply the exact Boolean-four-cube cardinality-layer formulas to the literal
-- source and defect partial evaluations used by the selected KKT construction.
-- Both partial families have zero empty placement, so each degree-summed
-- Möbius source/defect vector is a fixed linear combination of only the four
-- nonempty subset-cardinality layer sums.
--
-- Thus the G2 producer no longer needs to reason separately about fifteen
-- source atoms and fifteen defect atoms even before the Green pairing.  At each
-- multiplier coordinate the exact source/defect degree vectors are:
--
--   D1 = L1
--   D2 = L2 - 3 L1
--   D3 = L3 - 2 L2 + 3 L1
--   D4 = L4 - L3 + L2 - L1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact as Atoms
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusDegreeLayerExact as Layer

sourcePartialAt :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Multiplier → Cube.Subset4 → ℚ
sourcePartialAt partial row subset = Atoms.sourcePartial partial subset row

defectPartialAt :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Multiplier → Cube.Subset4 → ℚ
defectPartialAt partial row subset = Atoms.defectPartial partial subset row

sourceLayer1 sourceLayer2 sourceLayer3 sourceLayer4 :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Multiplier → ℚ
sourceLayer1 partial row = Layer.layer1 (sourcePartialAt partial row)
sourceLayer2 partial row = Layer.layer2 (sourcePartialAt partial row)
sourceLayer3 partial row = Layer.layer3 (sourcePartialAt partial row)
sourceLayer4 partial row = Layer.layer4 (sourcePartialAt partial row)

defectLayer1 defectLayer2 defectLayer3 defectLayer4 :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Multiplier → ℚ
defectLayer1 partial row = Layer.layer1 (defectPartialAt partial row)
defectLayer2 partial row = Layer.layer2 (defectPartialAt partial row)
defectLayer3 partial row = Layer.layer3 (defectPartialAt partial row)
defectLayer4 partial row = Layer.layer4 (defectPartialAt partial row)

sourceDegree1 sourceDegree2 sourceDegree3 sourceDegree4 :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Multiplier → ℚ
sourceDegree1 partial row = Layer.mobiusDegree1 (sourcePartialAt partial row)
sourceDegree2 partial row = Layer.mobiusDegree2 (sourcePartialAt partial row)
sourceDegree3 partial row = Layer.mobiusDegree3 (sourcePartialAt partial row)
sourceDegree4 partial row = Layer.mobiusDegree4 (sourcePartialAt partial row)

defectDegree1 defectDegree2 defectDegree3 defectDegree4 :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor} →
  Atoms.SelectedConstraintPartialEvaluationData
    {Multiplier} pseudoData firstVariationCovector rawExtractor →
  Multiplier → ℚ
defectDegree1 partial row = Layer.mobiusDegree1 (defectPartialAt partial row)
defectDegree2 partial row = Layer.mobiusDegree2 (defectPartialAt partial row)
defectDegree3 partial row = Layer.mobiusDegree3 (defectPartialAt partial row)
defectDegree4 partial row = Layer.mobiusDegree4 (defectPartialAt partial row)

sourceDegree1LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row → sourceDegree1 partial row ≡ sourceLayer1 partial row
sourceDegree1LayerExact partial row =
  Layer.mobiusDegree1ZeroBackground
    (sourcePartialAt partial row) (Atoms.sourceEmptyZero partial row)

sourceDegree2LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  sourceDegree2 partial row
  ≡ sourceLayer2 partial row - (+ 3 / 1) * sourceLayer1 partial row
sourceDegree2LayerExact partial row =
  Layer.mobiusDegree2ZeroBackground
    (sourcePartialAt partial row) (Atoms.sourceEmptyZero partial row)

sourceDegree3LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  sourceDegree3 partial row
  ≡ sourceLayer3 partial row
    - (+ 2 / 1) * sourceLayer2 partial row
    + (+ 3 / 1) * sourceLayer1 partial row
sourceDegree3LayerExact partial row =
  Layer.mobiusDegree3ZeroBackground
    (sourcePartialAt partial row) (Atoms.sourceEmptyZero partial row)

sourceDegree4LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  sourceDegree4 partial row
  ≡ sourceLayer4 partial row - sourceLayer3 partial row
    + sourceLayer2 partial row - sourceLayer1 partial row
sourceDegree4LayerExact partial row =
  Layer.mobiusDegree4ZeroBackground
    (sourcePartialAt partial row) (Atoms.sourceEmptyZero partial row)

defectDegree1LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row → defectDegree1 partial row ≡ defectLayer1 partial row
defectDegree1LayerExact partial row =
  Layer.mobiusDegree1ZeroBackground
    (defectPartialAt partial row) (Atoms.defectEmptyZero partial row)

defectDegree2LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  defectDegree2 partial row
  ≡ defectLayer2 partial row - (+ 3 / 1) * defectLayer1 partial row
defectDegree2LayerExact partial row =
  Layer.mobiusDegree2ZeroBackground
    (defectPartialAt partial row) (Atoms.defectEmptyZero partial row)

defectDegree3LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  defectDegree3 partial row
  ≡ defectLayer3 partial row
    - (+ 2 / 1) * defectLayer2 partial row
    + (+ 3 / 1) * defectLayer1 partial row
defectDegree3LayerExact partial row =
  Layer.mobiusDegree3ZeroBackground
    (defectPartialAt partial row) (Atoms.defectEmptyZero partial row)

defectDegree4LayerExact :
  ∀ {Multiplier pseudoData firstVariationCovector rawExtractor}
    (partial : Atoms.SelectedConstraintPartialEvaluationData
      {Multiplier} pseudoData firstVariationCovector rawExtractor)
    row →
  defectDegree4 partial row
  ≡ defectLayer4 partial row - defectLayer3 partial row
    + defectLayer2 partial row - defectLayer1 partial row
defectDegree4LayerExact partial row =
  Layer.mobiusDegree4ZeroBackground
    (defectPartialAt partial row) (Atoms.defectEmptyZero partial row)

selectedConstraintSourceDegreeLayerLevel : ProofLevel
selectedConstraintSourceDegreeLayerLevel = machineChecked

selectedConstraintDefectDegreeLayerLevel : ProofLevel
selectedConstraintDefectDegreeLayerLevel = machineChecked
