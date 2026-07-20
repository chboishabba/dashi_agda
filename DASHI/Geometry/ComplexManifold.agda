module DASHI.Geometry.ComplexManifold where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Complex-manifold charts and holomorphic transition laws.
--
-- This is a producer interface: a concrete manifold must supply chart
-- coverage, chart/image inverses, overlap transport, the cocycle laws, and
-- holomorphicity witnesses.  No analytic theorem is postulated here.

record ChartCover
    {Point : Set}
    (ChartIndex : Set)
    (Domain : ChartIndex → Point → Set)
    (x : Point)
    : Set where
  constructor mkChartCover
  field
    chartIndex : ChartIndex
    inDomain : Domain chartIndex x

open ChartCover public

record ComplexManifoldCharts (Point Coordinate : Set) : Set₁ where
  constructor mkComplexManifoldCharts
  field
    ChartIndex : Set
    Domain : ChartIndex → Point → Set

    cover : (x : Point) → ChartCover ChartIndex Domain x

    coordinate :
      (i : ChartIndex) →
      (x : Point) →
      Domain i x →
      Coordinate

    Image : ChartIndex → Coordinate → Set

    inverseCoordinate :
      ChartIndex →
      Coordinate →
      Point

    inverseInDomain :
      ∀ {i z} →
      Image i z →
      Domain i (inverseCoordinate i z)

    chartLeftInverse :
      (i : ChartIndex) →
      (x : Point) →
      (member : Domain i x) →
      inverseCoordinate i (coordinate i x member) ≡ x

    chartRightInverse :
      (i : ChartIndex) →
      (z : Coordinate) →
      (image : Image i z) →
      coordinate i (inverseCoordinate i z) (inverseInDomain image) ≡ z

    Overlap : ChartIndex → ChartIndex → Point → Set

    overlapReflexive :
      (i : ChartIndex) →
      (x : Point) →
      Domain i x →
      Overlap i i x

    overlapSymmetric :
      ∀ {i j x} →
      Overlap i j x →
      Overlap j i x

    transition :
      ChartIndex →
      ChartIndex →
      Coordinate →
      Coordinate

    transitionIdentity :
      (i : ChartIndex) →
      (z : Coordinate) →
      transition i i z ≡ z

    transitionInverse :
      ∀ {i j x} →
      Overlap i j x →
      (z : Coordinate) →
      transition j i (transition i j z) ≡ z

    transitionCocycle :
      ∀ {i j k x} →
      Overlap i j x →
      Overlap j k x →
      Overlap i k x →
      (z : Coordinate) →
      transition j k (transition i j z) ≡ transition i k z

    coordinateChange :
      ∀ {i j x} →
      (leftMember : Domain i x) →
      (rightMember : Domain j x) →
      Overlap i j x →
      coordinate j x rightMember ≡ transition i j (coordinate i x leftMember)

open ComplexManifoldCharts public

record HolomorphicTransitionLaws
    {Point Coordinate : Set}
    (charts : ComplexManifoldCharts Point Coordinate)
    : Set₁ where
  open ComplexManifoldCharts charts

  field
    Holomorphic : (Coordinate → Coordinate) → Set

    holomorphicIdentity :
      Holomorphic (λ z → z)

    holomorphicComposition :
      ∀ {f g : Coordinate → Coordinate} →
      Holomorphic f →
      Holomorphic g →
      Holomorphic (λ z → g (f z))

    transitionHolomorphic :
      ∀ {i j x} →
      Overlap i j x →
      Holomorphic (transition i j)

open HolomorphicTransitionLaws public

record ComplexManifoldAuthority (Point Coordinate : Set) : Set₁ where
  constructor mkComplexManifoldAuthority
  field
    complexDimension : Nat
    complexCharts : ComplexManifoldCharts Point Coordinate
    holomorphicTransitions : HolomorphicTransitionLaws complexCharts

open ComplexManifoldAuthority public

inverseTransitionHolomorphic :
  ∀ {Point Coordinate : Set}
    (M : ComplexManifoldAuthority Point Coordinate)
    {i j x} →
    Overlap (complexCharts M) i j x →
    Holomorphic (holomorphicTransitions M)
      (transition (complexCharts M) j i)
inverseTransitionHolomorphic M overlap =
  transitionHolomorphic
    (holomorphicTransitions M)
    (overlapSymmetric (complexCharts M) overlap)
