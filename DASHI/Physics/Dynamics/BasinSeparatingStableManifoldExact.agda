{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.BasinSeparatingStableManifoldExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as BRR

------------------------------------------------------------------------
-- Stable-manifold basin separator.
--
-- Invariance of a manifold alone does not imply that it is a basin boundary.
-- The extra theorem needed by singular-funnel certification is explicitly
-- two-sided: selected states on opposite sides of the manifold belong to
-- opposite basin classes.
------------------------------------------------------------------------

data SeparatorSide : Set where
  negativeSide : SeparatorSide
  onSeparator : SeparatorSide
  positiveSide : SeparatorSide

record StableManifoldCrossSection
  (State Coordinate : Set) : Set₁ where
  field
    coordinate : State → Coordinate
    separatorCoordinate : Coordinate
    side : State → SeparatorSide

open StableManifoldCrossSection public

record TwoBasinSeparatorLaw
  {State Coordinate : Set}
  (section : StableManifoldCrossSection State Coordinate)
  (LowerBasin UpperBasin : State → Set) : Set₁ where
  field
    negativeImpliesLower :
      ∀ state →
      side section state ≡ negativeSide →
      LowerBasin state

    positiveImpliesUpper :
      ∀ state →
      side section state ≡ positiveSide →
      UpperBasin state

    lowerExcludesUpper :
      ∀ state →
      LowerBasin state →
      ¬ UpperBasin state

    upperExcludesLower :
      ∀ state →
      UpperBasin state →
      ¬ LowerBasin state

open TwoBasinSeparatorLaw public

record CrossingBracket
  {State Coordinate : Set}
  (section : StableManifoldCrossSection State Coordinate) : Set where
  field
    lowerEndpoint : State
    upperEndpoint : State
    lowerOnNegativeSide :
      side section lowerEndpoint ≡ negativeSide
    upperOnPositiveSide :
      side section upperEndpoint ≡ positiveSide

open CrossingBracket public

crossing-bracket-gives-opposite-lower-membership :
  ∀ {State Coordinate : Set}
    {section : StableManifoldCrossSection State Coordinate}
    {LowerBasin UpperBasin : State → Set} →
  (law : TwoBasinSeparatorLaw section LowerBasin UpperBasin) →
  (crossing : CrossingBracket section) →
  LowerBasin (lowerEndpoint crossing)
  ×
  ¬ LowerBasin (upperEndpoint crossing)
crossing-bracket-gives-opposite-lower-membership law crossing =
  negativeImpliesLower law
    (lowerEndpoint crossing)
    (lowerOnNegativeSide crossing)
  ,
  upperExcludesLower law
    (upperEndpoint crossing)
    (positiveImpliesUpper law
      (upperEndpoint crossing)
      (upperOnPositiveSide crossing))

------------------------------------------------------------------------
-- Resolution attachment.
--
-- If the two certified sides are also within a declared resolution, the
-- crossing becomes a BasinBoundaryResolutionWitness immediately.
------------------------------------------------------------------------

record ResolvedCrossingBracket
  {State Coordinate Resolution : Set}
  (section : StableManifoldCrossSection State Coordinate)
  (geometry : BRR.ResolutionGeometry State Resolution)
  (resolution : Resolution) : Set where
  field
    crossing : CrossingBracket section
    endpointsNear :
      BRR.Near geometry resolution
        (lowerEndpoint crossing)
        (upperEndpoint crossing)

open ResolvedCrossingBracket public

resolved-crossing-gives-boundary-witness :
  ∀ {State Coordinate Resolution : Set}
    {section : StableManifoldCrossSection State Coordinate}
    {geometry : BRR.ResolutionGeometry State Resolution}
    {resolution : Resolution}
    {LowerBasin UpperBasin : State → Set} →
  TwoBasinSeparatorLaw section LowerBasin UpperBasin →
  ResolvedCrossingBracket section geometry resolution →
  BRR.BasinBoundaryResolutionWitness
    geometry LowerBasin resolution
resolved-crossing-gives-boundary-witness law resolved =
  let
    crossingWitness = crossing resolved
    opposite =
      crossing-bracket-gives-opposite-lower-membership
        law crossingWitness
  in
  record
    { inside = lowerEndpoint crossingWitness
    ; outside = upperEndpoint crossingWitness
    ; withinResolution = endpointsNear resolved
    ; insideHas = fst opposite
    ; outsideLacks = snd opposite
    }

resolved-crossing-refutes-robustness :
  ∀ {State Coordinate Resolution : Set}
    {section : StableManifoldCrossSection State Coordinate}
    {geometry : BRR.ResolutionGeometry State Resolution}
    {resolution : Resolution}
    {LowerBasin UpperBasin : State → Set} →
  (law : TwoBasinSeparatorLaw section LowerBasin UpperBasin) →
  (resolved : ResolvedCrossingBracket section geometry resolution) →
  ¬ BRR.RobustAt
      geometry LowerBasin resolution
      (lowerEndpoint (crossing resolved))
resolved-crossing-refutes-robustness law resolved =
  BRR.boundary-witness-refutes-robustness
    (resolved-crossing-gives-boundary-witness law resolved)
