module DASHI.Visualisation.GraphSeriesSemanticExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Bar data and rendering marks.  Relabelling is equivariant, not pixelwise
-- invariant: swapping source categories swaps the rendered marks.

record BarDatum : Set where
  constructor barDatum
  field
    firstBarValue : Nat
    secondBarValue : Nat

open BarDatum public

swapBars : BarDatum → BarDatum
swapBars datum =
  barDatum
    (secondBarValue datum)
    (firstBarValue datum)

renderBarMarks : BarDatum → Nat × Nat
renderBarMarks datum =
  firstBarValue datum , secondBarValue datum

swapMarks : Nat × Nat → Nat × Nat
swapMarks (first , second) = second , first

barRelabellingEquivariant :
  (datum : BarDatum) →
  renderBarMarks (swapBars datum)
  ≡
  swapMarks (renderBarMarks datum)
barRelabellingEquivariant (barDatum first second) = refl

aggregateBars : BarDatum → Nat
aggregateBars datum =
  firstBarValue datum + secondBarValue datum

barAggregationPreservesValue :
  aggregateBars (barDatum 3 4) ≡ 7
barAggregationPreservesValue = refl

------------------------------------------------------------------------
-- Ordered line series.  Temporal order is part of the carrier.

data TimePoint : Set where
  earlyTime : TimePoint
  middleTime : TimePoint
  lateTime : TimePoint

data OrderedBefore : TimePoint → TimePoint → Set where
  earlyBeforeMiddle : OrderedBefore earlyTime middleTime
  middleBeforeLate : OrderedBefore middleTime lateTime
  earlyBeforeLate : OrderedBefore earlyTime lateTime

record LineSeries : Set where
  constructor lineSeries
  field
    earlyValue : Nat
    middleValue : Nat
    lateValue : Nat

canonicalLineSeries : LineSeries
canonicalLineSeries = lineSeries 2 5 3

lineOrderWitness :
  OrderedBefore earlyTime middleTime
  ×
  OrderedBefore middleTime lateTime
lineOrderWitness = earlyBeforeMiddle , middleBeforeLate

------------------------------------------------------------------------
-- Two-node graph energy.  The graph relabelling swaps node labels while the
-- declared symmetric energy remains equal.

data Vertex : Set where
  vertexLeft : Vertex
  vertexRight : Vertex

record Layout2 : Set where
  constructor layout2
  field
    leftPosition : Nat
    rightPosition : Nat

open Layout2 public

swapLayout : Layout2 → Layout2
swapLayout layout =
  layout2
    (rightPosition layout)
    (leftPosition layout)

symmetricEnergy : Layout2 → Nat
symmetricEnergy (layout2 left right) =
  left * left + right * right + left * right

energyRelabellingEquivariantGeneric :
  (layout : Layout2) →
  symmetricEnergy (swapLayout layout)
  ≡
  symmetricEnergy layout
energyRelabellingEquivariantGeneric (layout2 left right) =
  trans
    (cong
      (λ squareSum → squareSum + right * left)
      (+-comm (right * right) (left * left)))
    (cong
      (λ crossTerm → left * left + right * right + crossTerm)
      (*-comm right left))

energyRelabellingEquivariant :
  symmetricEnergy (swapLayout (layout2 2 3))
  ≡
  symmetricEnergy (layout2 2 3)
energyRelabellingEquivariant =
  energyRelabellingEquivariantGeneric (layout2 2 3)

data LayoutConfiguration : Set where
  fixedSeedConfiguration : LayoutConfiguration
  alternateSeedConfiguration : LayoutConfiguration

record GraphSeriesSemanticBoundary : Set where
  constructor graphSeriesSemanticBoundary
  field
    barRelabellingLeavesPixelArrayIdentical : Bool
    barRelabellingLeavesPixelArrayIdenticalIsFalse :
      barRelabellingLeavesPixelArrayIdentical ≡ false

    graphIsomorphismForcesEveryLocalLayoutRunEqual : Bool
    graphIsomorphismForcesEveryLocalLayoutRunEqualIsFalse :
      graphIsomorphismForcesEveryLocalLayoutRunEqual ≡ false

    increasingOneEdgeWeightUniversallyShortensThatEdge : Bool
    increasingOneEdgeWeightUniversallyShortensThatEdgeIsFalse :
      increasingOneEdgeWeightUniversallyShortensThatEdge ≡ false

    customReciprocalEnergyIsExactlyFruchtermanReingold : Bool
    customReciprocalEnergyIsExactlyFruchtermanReingoldIsFalse :
      customReciprocalEnergyIsExactlyFruchtermanReingold ≡ false

open GraphSeriesSemanticBoundary public

canonicalGraphSeriesSemanticBoundary :
  GraphSeriesSemanticBoundary
canonicalGraphSeriesSemanticBoundary =
  graphSeriesSemanticBoundary
    false refl
    false refl
    false refl
    false refl
