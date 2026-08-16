module DASHI.Cognition.PNF.FinitePathTransitionOptimalityExact where

------------------------------------------------------------------------
-- Generic path-geometry theorem behind the Wave4 Gray-code regression.
-- Every edge of an injective code path has positive distance, so an n-edge
-- path costs at least n.  Any realization with unit distance on every edge
-- attains that bound and is therefore transition-optimal.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OrientedZeroGrayTransitionGeometryExact as WaveGray

edgeCount : List Nat → Nat
edgeCount [] = 0
edgeCount (d ∷ ds) = suc (edgeCount ds)

pathCost : List Nat → Nat
pathCost [] = 0
pathCost (d ∷ ds) = d + pathCost ds

data PositiveEdges : List Nat → Set where
  positiveNil : PositiveEdges []
  positiveCons : ∀ {d ds} → 1 ≤ d → PositiveEdges ds → PositiveEdges (d ∷ ds)

positivePathCostLowerBound : ∀ {ds} → PositiveEdges ds →
  edgeCount ds ≤ pathCost ds
positivePathCostLowerBound positiveNil = z≤n
positivePathCostLowerBound (positiveCons dPositive restPositive) =
  +-mono-≤ dPositive (positivePathCostLowerBound restPositive)

unitEdges : Nat → List Nat
unitEdges zero = []
unitEdges (suc n) = 1 ∷ unitEdges n

unitEdgesPositive : (n : Nat) → PositiveEdges (unitEdges n)
unitEdgesPositive zero = positiveNil
unitEdgesPositive (suc n) = positiveCons (s≤s z≤n) (unitEdgesPositive n)

unitEdgesCount : (n : Nat) → edgeCount (unitEdges n) ≡ n
unitEdgesCount zero = refl
unitEdgesCount (suc n) rewrite unitEdgesCount n = refl

unitEdgesCost : (n : Nat) → pathCost (unitEdges n) ≡ n
unitEdgesCost zero = refl
unitEdgesCost (suc n) rewrite unitEdgesCost n = refl

unitDistancePathIsOptimal :
  (n : Nat) (competitor : List Nat) →
  PositiveEdges competitor →
  edgeCount competitor ≡ n →
  pathCost (unitEdges n) ≤ pathCost competitor
unitDistancePathIsOptimal n competitor positive sameCount
  rewrite unitEdgesCost n | sym sameCount =
  positivePathCostLowerBound positive

------------------------------------------------------------------------
-- Existing Wave4 is the n=3 instance.
------------------------------------------------------------------------

waveGrayDistances : List Nat
waveGrayDistances = 1 ∷ 1 ∷ 1 ∷ []

waveBinaryDistances : List Nat
waveBinaryDistances = 1 ∷ 2 ∷ 1 ∷ []

waveGrayIsUnitPath : waveGrayDistances ≡ unitEdges 3
waveGrayIsUnitPath = refl

waveBinaryPositive : PositiveEdges waveBinaryDistances
waveBinaryPositive =
  positiveCons (s≤s z≤n)
    (positiveCons (s≤s z≤n)
      (positiveCons (s≤s z≤n) positiveNil))

waveGrayOptimalAgainstBinary :
  pathCost waveGrayDistances ≤ pathCost waveBinaryDistances
waveGrayOptimalAgainstBinary =
  unitDistancePathIsOptimal 3 waveBinaryDistances waveBinaryPositive refl

waveGrayCostMatchesExistingTheorem :
  pathCost waveGrayDistances ≡ WaveGray.grayPathDistortion
waveGrayCostMatchesExistingTheorem = refl

waveBinaryCostMatchesExistingTheorem :
  pathCost waveBinaryDistances ≡ WaveGray.binaryPathDistortion
waveBinaryCostMatchesExistingTheorem = refl

------------------------------------------------------------------------
-- Geometry boundary: an actual embedding theorem must separately prove that
-- injectivity implies positive edge distance for its chosen code metric, and
-- that a unit-edge/Gray path exists in the target code space.  This theorem
-- owns the universal path-cost step once those facts are supplied.
------------------------------------------------------------------------
