module DASHI.Moonshine.LeechWeightTwo196608AuthorityCorrectionExact where

------------------------------------------------------------------------
-- AUTHORITY CORRECTION
--
-- The earlier module proves a legitimate basis-dependent coordinate count
--
--   196608 = 196560 + 24 + 24,
--   196884 = 196608 + 276.
--
-- This file prevents that chart from being mistaken for the FLM orbifold
-- decomposition.  The sourced sector decomposition is instead
--
--   196884 = 98580 + 98304.
--
-- The two presentations have the same total but different summands and
-- different authority.  No action or invariant filtration is transported
-- between them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.LeechWeightTwo196608BridgeExact as Old
import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as Orbifold

bothChartsReconstructWeightTwo :
  Old.leechCoordinateSubtotal + Old.offDiagonalQuadraticCount
  ≡ Orbifold.untwistedInvariantWeightTwoDimension
    + Orbifold.twistedInvariantWeightTwoDimension
bothChartsReconstructWeightTwo = refl

coordinateSubtotalDiffersFromUntwistedSummand :
  Old.leechCoordinateSubtotal
  ≡ Orbifold.untwistedInvariantWeightTwoDimension → ⊥
coordinateSubtotalDiffersFromUntwistedSummand ()

coordinateSubtotalDiffersFromTwistedSummand :
  Old.leechCoordinateSubtotal
  ≡ Orbifold.twistedInvariantWeightTwoDimension → ⊥
coordinateSubtotalDiffersFromTwistedSummand ()

offDiagonalCountIsNotTwistedSummand :
  Old.offDiagonalQuadraticCount
  ≡ Orbifold.twistedInvariantWeightTwoDimension → ⊥
offDiagonalCountIsNotTwistedSummand ()

record Leech196608AuthorityCorrection : Set where
  constructor leech-196608-authority-correction
  field
    coordinateChartTotalWitness :
      Old.leechCoordinateSubtotal + Old.offDiagonalQuadraticCount
      ≡ 196884
    orbifoldChartTotalWitness :
      Orbifold.untwistedInvariantWeightTwoDimension
      + Orbifold.twistedInvariantWeightTwoDimension
      ≡ 196884
    coordinateSubtotalNotUntwistedWitness :
      Old.leechCoordinateSubtotal
      ≡ Orbifold.untwistedInvariantWeightTwoDimension → ⊥
    coordinateSubtotalNotTwistedWitness :
      Old.leechCoordinateSubtotal
      ≡ Orbifold.twistedInvariantWeightTwoDimension → ⊥
    coordinateChartIsPublishedFLMOrbifoldDecomposition : Bool
    coordinateChartIsPublishedFLMOrbifoldDecompositionIsFalse :
      coordinateChartIsPublishedFLMOrbifoldDecomposition ≡ false
    coordinateChartProvidesMonsterInvariantFiltration : Bool
    coordinateChartProvidesMonsterInvariantFiltrationIsFalse :
      coordinateChartProvidesMonsterInvariantFiltration ≡ false

canonicalLeech196608AuthorityCorrection :
  Leech196608AuthorityCorrection
canonicalLeech196608AuthorityCorrection =
  leech-196608-authority-correction
    Old.subtotalPlusOffDiagonalIsWeightTwo
    Orbifold.publishedOrbifoldWeightTwoSplit
    coordinateSubtotalDiffersFromUntwistedSummand
    coordinateSubtotalDiffersFromTwistedSummand
    false refl
    false refl
