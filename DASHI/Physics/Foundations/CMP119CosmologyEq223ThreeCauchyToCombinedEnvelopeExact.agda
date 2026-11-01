{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223ThreeCauchyToCombinedEnvelopeExact where

------------------------------------------------------------------------
-- OLD THREE-SECTOR CAUCHY PRODUCER -> NEW COMBINED E/R/B ENVELOPE.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as Combined
import DASHI.Physics.Foundations.CMP119CosmologyEq223DiagonalCauchyMajorantExact as Cauchy
import DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact as Dominance
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

module _
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {scale : Nat}
    (realization :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration scale)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
  where

  module C = Cauchy realization measure orderLaws
  module E = Combined realization measure orderLaws partition scaleLaw

  threeTraceUpper : C.UniformDiagonalCauchyUpperBounds → ℚ
  threeTraceUpper bounds =
    (C.fourTimes (C.regularPerDiagonalUpper bounds)
      + C.fourTimes (C.rOperationPerDiagonalUpper bounds))
      + C.fourTimes (C.boundaryPerDiagonalUpper bounds)

  threeTraceUpperIsCauchyTotal :
    (bounds : C.UniformDiagonalCauchyUpperBounds) →
    threeTraceUpper bounds ≡
      C.fourTimes
        ((C.regularPerDiagonalUpper bounds
          + C.rOperationPerDiagonalUpper bounds)
          + C.boundaryPerDiagonalUpper bounds)
  threeTraceUpperIsCauchyTotal bounds =
    Ring.solve-∀
      (C.regularPerDiagonalUpper bounds)
      (C.rOperationPerDiagonalUpper bounds)
      (C.boundaryPerDiagonalUpper bounds)

  combinedTraceBelowThreeTraceUpper :
    (bounds : C.UniformDiagonalCauchyUpperBounds) →
    ∀ configuration →
    E.combinedERBDiagonalTrace configuration
      ≤ threeTraceUpper bounds
  combinedTraceBelowThreeTraceUpper bounds configuration =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (C.regularTraceBelowFourTimes bounds configuration)
        (C.rOperationTraceBelowFourTimes bounds configuration))
      (C.boundaryTraceBelowFourTimes bounds configuration)

  asCombinedERBEnvelope :
    C.UniformDiagonalCauchyUpperBounds →
    E.CombinedERBTraceEnvelope
  asCombinedERBEnvelope bounds = record
    { E.CombinedERBTraceEnvelope.combinedUpper =
        C.fourTimes
          ((C.regularPerDiagonalUpper bounds
            + C.rOperationPerDiagonalUpper bounds)
            + C.boundaryPerDiagonalUpper bounds)
    ; E.CombinedERBTraceEnvelope.combinedTraceBelow =
        λ configuration →
          subst
            (λ right → E.combinedERBDiagonalTrace configuration ≤ right)
            (threeTraceUpperIsCauchyTotal bounds)
            (combinedTraceBelowThreeTraceUpper bounds configuration)
    }

  oldCauchyScalarMarginForcesLiteralDominance :
    (bounds : C.UniformDiagonalCauchyUpperBounds) →
    C.fourTimes
      ((C.regularPerDiagonalUpper bounds
        + C.rOperationPerDiagonalUpper bounds)
        + C.boundaryPerDiagonalUpper bounds)
      < - Eq223.eq223VacuumTraceCoefficient realization →
    Dominance.LiteralNegativeSectorDominance realization measure
  oldCauchyScalarMarginForcesLiteralDominance bounds margin =
    E.combinedEnvelopeVacuumMarginForcesLiteralDominance
      (asCombinedERBEnvelope bounds) margin

  threeCauchyConstantsAreNotTerminalCosmologyCoordinates : Bool
  threeCauchyConstantsAreNotTerminalCosmologyCoordinates = true

  combinedEnvelopeIsTheTerminalSourceCoordinate : Bool
  combinedEnvelopeIsTheTerminalSourceCoordinate = true
