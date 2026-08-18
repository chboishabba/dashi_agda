module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintGramBlockSchurExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Expose the exact 12-average / 765-reduced-gauge block structure hidden in
-- the selected 780-row KKT Gram before applying any locality majorant.
--
-- For a reduced multiplier (alpha,gamma), reopening gives the literal tagged
-- row vector consumed by K_A=L_A L_A^*.  The already-proved same-object
-- adjoint decomposition is
--
--   L_A^*(alpha,gamma) = A^* alpha + G_A^* gamma.
--
-- Applying the two tagged row families gives exactly
--
--   average block:
--     256 alpha + A G_A^* gamma,
--
--   gauge block:
--     G_A A^* alpha + K_g,A gamma.
--
-- Thus the full selected multiplier Green need not be treated as an opaque
-- 780-row operator.  The average diagonal is explicitly invertible with
-- inverse 1/256, the gauge diagonal is the already-decomposed local gauge
-- Gram, and only the two finite-rank cross maps remain to be Schur-completed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact as AverageSection
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as KKT
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedReducedCombinedConstraintFloorExact as Floor
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact as GaugeOperator

ReducedMultiplier : Set
ReducedMultiplier = Split.SelectedReducedCombinedMultiplier

rawOf : ReducedMultiplier → Combined.SelectedConstraintRow4 → ℚ
rawOf = Split.reopenReducedMultiplier

combinedGramApply :
  Physical.RationalSU2Background4 → ReducedMultiplier →
  Combined.SelectedConstraintRow4 → ℚ
combinedGramApply background selected =
  KKT.selectedCombinedConstraintGramApply background (rawOf selected)

averageGaugeCross :
  Physical.RationalSU2Background4 → ReducedMultiplier →
  Average.SelectedBlockAverageRow4 → ℚ
averageGaugeCross background selected =
  Average.selectedBackgroundBlockAverageConstraintApply
    (Floor.backgroundGaugeAdjoint background selected)

gaugeAverageCross :
  Physical.RationalSU2Background4 → ReducedMultiplier →
  DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact.GaugeCoordinate4 → ℚ
gaugeAverageCross background selected =
  GaugeOperator.backgroundGaugeConstraintApply background
    (Floor.averageAdjoint selected)

combinedGramAverageBlockExact :
  ∀ background selected row →
  combinedGramApply background selected (Combined.averageConstraintRow row)
  ≡ AverageSection.siteCount * Split.averageMultiplier selected row
    + averageGaugeCross background selected row
combinedGramAverageBlockExact background selected row =
  let
    raw = rawOf selected
    adjoint = KKT.selectedCombinedConstraintTransposeApply background raw
    assembled = Floor.assembledBackgroundCombinedAdjoint background selected

    gramAction = KKT.selectedCombinedConstraintGramActionExact
      background raw (Combined.averageConstraintRow row)

    sameAdjoint : ∀ coordinate → adjoint coordinate ≡ assembled coordinate
    sameAdjoint = Floor.selectedReducedCombinedAdjointSameObject background selected

    moveToAssembled :
      Combined.selectedBackgroundCombinedConstraintApply background adjoint
        (Combined.averageConstraintRow row)
      ≡ Combined.selectedBackgroundCombinedConstraintApply background assembled
        (Combined.averageConstraintRow row)
    moveToAssembled =
      Rect.applyRectangularVectorCong StateCarrier.physicalStateCarrier
        (Combined.selectedBackgroundLinearizedConstraintMatrix background)
        sameAdjoint (Combined.averageConstraintRow row)

    splitAverage :
      Average.selectedBackgroundBlockAverageConstraintApply assembled row
      ≡ Average.selectedBackgroundBlockAverageConstraintApply
          (Floor.averageAdjoint selected) row
        + Average.selectedBackgroundBlockAverageConstraintApply
          (Floor.backgroundGaugeAdjoint background selected) row
    splitAverage =
      Rect.applyRectangularAddExact StateCarrier.physicalStateCarrier
        Average.selectedBackgroundBlockAverageConstraintMatrix
        (Floor.averageAdjoint selected)
        (Floor.backgroundGaugeAdjoint background selected) row

    normalExact :
      Average.selectedBackgroundBlockAverageConstraintApply
          (Floor.averageAdjoint selected) row
      ≡ AverageSection.siteCount * Split.averageMultiplier selected row
    normalExact = AverageSection.selectedBlockAverageNormalExact
      (Split.averageMultiplier selected) row
  in
  trans gramAction
    (trans moveToAssembled
      (trans splitAverage
        (cong
          (_+ averageGaugeCross background selected row)
          normalExact)))

combinedGramGaugeBlockExact :
  ∀ background selected row →
  combinedGramApply background selected (Combined.gaugeConstraintRow row)
  ≡ gaugeAverageCross background selected row
    + GaugeOperator.backgroundGaugeGramApply background
        (Split.gaugeMultiplier selected) row
combinedGramGaugeBlockExact background selected row =
  let
    raw = rawOf selected
    adjoint = KKT.selectedCombinedConstraintTransposeApply background raw
    assembled = Floor.assembledBackgroundCombinedAdjoint background selected

    gramAction = KKT.selectedCombinedConstraintGramActionExact
      background raw (Combined.gaugeConstraintRow row)

    sameAdjoint : ∀ coordinate → adjoint coordinate ≡ assembled coordinate
    sameAdjoint = Floor.selectedReducedCombinedAdjointSameObject background selected

    moveToAssembled :
      Combined.selectedBackgroundCombinedConstraintApply background adjoint
        (Combined.gaugeConstraintRow row)
      ≡ Combined.selectedBackgroundCombinedConstraintApply background assembled
        (Combined.gaugeConstraintRow row)
    moveToAssembled =
      Rect.applyRectangularVectorCong StateCarrier.physicalStateCarrier
        (Combined.selectedBackgroundLinearizedConstraintMatrix background)
        sameAdjoint (Combined.gaugeConstraintRow row)

    splitGauge :
      GaugeOperator.backgroundGaugeConstraintApply background assembled row
      ≡ GaugeOperator.backgroundGaugeConstraintApply background
          (Floor.averageAdjoint selected) row
        + GaugeOperator.backgroundGaugeConstraintApply background
          (Floor.backgroundGaugeAdjoint background selected) row
    splitGauge =
      GaugeOperator.backgroundGaugeConstraintAdd background
        (Floor.averageAdjoint selected)
        (Floor.backgroundGaugeAdjoint background selected) row
  in
  trans gramAction
    (trans moveToAssembled splitGauge)

selectedCombinedGramBlockSchurSurfaceLevel : ProofLevel
selectedCombinedGramBlockSchurSurfaceLevel = machineChecked

-- The remaining analytic locality theorem may now Schur-complement the exact
-- 256 I average block instead of applying a 780-row black-box CT estimate.
selectedCombinedGramSchurLocalityProducerLevel : ProofLevel
selectedCombinedGramSchurLocalityProducerLevel = conditional
