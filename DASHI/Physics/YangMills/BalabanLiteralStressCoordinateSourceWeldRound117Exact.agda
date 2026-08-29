{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralStressCoordinateSourceWeldRound117Exact where

------------------------------------------------------------------------
-- ROUND117: THE SAME STRESS COORDINATE ALSO OWNS THE NORMALIZED SOURCE WELD
--
-- Round114 already forces the CMP119 telescope, shell/coefficient partition,
-- and marked Schwinger completion to be views of one selected stress coordinate.
-- Round116 isolates the finite normalized source-derivative algebra.  This file
-- makes that normalized metric/source weld a fourth view of the SAME coordinate.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record LiteralStressCoordinateSourceWeld
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    stressCoordinate : R114.LiteralStressCoordinate Y group

    -- Fourth source-native view of the exact same selected coordinate.
    asNormalizedMetricInsertion :
      R114.StressCoordinate stressCoordinate →
      R116.MetricStressNormalizedInsertionWeld
open LiteralStressCoordinateSourceWeld public

selectedNormalizedMetricInsertion :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C} →
  LiteralStressCoordinateSourceWeld Y group →
  R116.MetricStressNormalizedInsertionWeld
selectedNormalizedMetricInsertion dataSet =
  asNormalizedMetricInsertion dataSet
    (R114.coordinate (stressCoordinate dataSet))

selectedMetricVariationIsCMP119StressInsertion :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : LiteralStressCoordinateSourceWeld Y group) →
  R116.metricFirstVariationCrossNumerator
    (selectedNormalizedMetricInsertion dataSet)
  ≡ R116.cmp119StressInsertionNumerator
      (selectedNormalizedMetricInsertion dataSet)
selectedMetricVariationIsCMP119StressInsertion dataSet =
  R116.metricVariationCrossNumeratorIsCMP119StressInsertion
    (selectedNormalizedMetricInsertion dataSet)

literalStressCoordinateSourceWeldCompilerLevel : ProofLevel
literalStressCoordinateSourceWeldCompilerLevel = machineChecked

-- Physical instantiation now has one target object: construct the literal
-- CMP116 stress coordinate and show that its normalized metric derivative,
-- CMP119 telescope insertion, Row-B shell coefficients, and marked completion
-- are all the four views carried by `stressCoordinate` above.
literalCMP116CMP119StressCoordinateSourceInstantiationLevel : ProofLevel
literalCMP116CMP119StressCoordinateSourceInstantiationLevel = conditional
