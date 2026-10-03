{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223PointwiseToNumeratorMajorantExact where

------------------------------------------------------------------------
-- POINTWISE FOUR-DIAGONAL E/R/B BOUNDS -> EXACT WEIGHTED NUMERATOR MAJORANTS.
--
-- CMP119/CMP116 source bounds are analytic/local pointwise bounds before Haar
-- averaging.  The sign consumer, however, needs bounds on the weighted finite
-- numerators N_E,N_R,N_B.  Positive-Haar monotonicity is the only missing
-- algebra between those two levels.
--
-- This owner performs that transport on the EXACT Eq.(2.23) metric-variation
-- traces.  The remaining source theorem is now cleanly pointwise/Cauchy-shaped.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

import DASHI.Physics.Foundations.CMP119CosmologyEq223ERBUpperMajorantExact as ERB
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

open import Agda.Builtin.Nat using (Nat)

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
  where

  d = Eq223.sourceCompleteFiniteMetricVariation realization

  record PointwiseERBDiagonalTraceUpperBounds : Set where
    field
      regularPointwiseUpper : ℚ
      rOperationPointwiseUpper : ℚ
      boundaryPointwiseUpper : ℚ

      regularTraceBelow : ∀ configuration →
        Sector.regularDiagonalTrace d configuration
        ≤ regularPointwiseUpper

      rOperationTraceBelow : ∀ configuration →
        Sector.rOperationDiagonalTrace d configuration
        ≤ rOperationPointwiseUpper

      boundaryTraceBelow : ∀ configuration →
        Sector.boundaryDiagonalTrace d configuration
        ≤ boundaryPointwiseUpper

  open PointwiseERBDiagonalTraceUpperBounds public

  regularWeightedUpper : PointwiseERBDiagonalTraceUpperBounds → ℚ
  regularWeightedUpper bounds =
    Order.weightedNumerator measure
      (Order.constantObservable (regularPointwiseUpper bounds))

  rOperationWeightedUpper : PointwiseERBDiagonalTraceUpperBounds → ℚ
  rOperationWeightedUpper bounds =
    Order.weightedNumerator measure
      (Order.constantObservable (rOperationPointwiseUpper bounds))

  boundaryWeightedUpper : PointwiseERBDiagonalTraceUpperBounds → ℚ
  boundaryWeightedUpper bounds =
    Order.weightedNumerator measure
      (Order.constantObservable (boundaryPointwiseUpper bounds))

  regularNumeratorBelowWeightedUpper :
    (bounds : PointwiseERBDiagonalTraceUpperBounds) →
    Sector.regularNumerator measure d ≤ regularWeightedUpper bounds
  regularNumeratorBelowWeightedUpper bounds =
    Order.weightedNumeratorBelowConstant
      orderLaws
      (Sector.regularDiagonalTrace d)
      (regularPointwiseUpper bounds)
      (regularTraceBelow bounds)

  rOperationNumeratorBelowWeightedUpper :
    (bounds : PointwiseERBDiagonalTraceUpperBounds) →
    Sector.rOperationNumerator measure d ≤ rOperationWeightedUpper bounds
  rOperationNumeratorBelowWeightedUpper bounds =
    Order.weightedNumeratorBelowConstant
      orderLaws
      (Sector.rOperationDiagonalTrace d)
      (rOperationPointwiseUpper bounds)
      (rOperationTraceBelow bounds)

  boundaryNumeratorBelowWeightedUpper :
    (bounds : PointwiseERBDiagonalTraceUpperBounds) →
    Sector.boundaryNumerator measure d ≤ boundaryWeightedUpper bounds
  boundaryNumeratorBelowWeightedUpper bounds =
    Order.weightedNumeratorBelowConstant
      orderLaws
      (Sector.boundaryDiagonalTrace d)
      (boundaryPointwiseUpper bounds)
      (boundaryTraceBelow bounds)

  asLiteralERBUpperMajorants :
    PointwiseERBDiagonalTraceUpperBounds →
    ERB.LiteralERBUpperMajorants realization measure
  asLiteralERBUpperMajorants bounds = record
    { ERB.LiteralERBUpperMajorants.regularUpper =
        regularWeightedUpper bounds
    ; ERB.LiteralERBUpperMajorants.rOperationUpper =
        rOperationWeightedUpper bounds
    ; ERB.LiteralERBUpperMajorants.boundaryUpper =
        boundaryWeightedUpper bounds
    ; ERB.LiteralERBUpperMajorants.regularBelowUpper =
        regularNumeratorBelowWeightedUpper bounds
    ; ERB.LiteralERBUpperMajorants.rOperationBelowUpper =
        rOperationNumeratorBelowWeightedUpper bounds
    ; ERB.LiteralERBUpperMajorants.boundaryBelowUpper =
        boundaryNumeratorBelowWeightedUpper bounds
    }

pointwiseCauchyBoundsNowSufficeForERBNumeratorMajorants : Bool
pointwiseCauchyBoundsNowSufficeForERBNumeratorMajorants = true

noIndependentIntegratedSectorBoundRemains : Bool
noIndependentIntegratedSectorBoundRemains = true
