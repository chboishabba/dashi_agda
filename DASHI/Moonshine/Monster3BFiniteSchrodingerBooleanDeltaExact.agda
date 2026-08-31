module DASHI.Moonshine.Monster3BFiniteSchrodingerBooleanDeltaExact where

------------------------------------------------------------------------
-- BOOLEAN DELTA BRIDGE AND UNIT-TRANSLATION COVARIANCE
--
-- The earlier weight-projector lane already uses the six-coordinate Boolean
-- equality on X6 and proves its translation covariance.  This owner bridges
-- the comparison-defined delta used by the new Fourier-extraction proof to the
-- same Boolean support surface, then proves T_i delta_x = delta_{T_i x}
-- pointwise for every one of the six translation generators.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergPermutationExact as Perm
import DASHI.Moonshine.Monster3BFiniteWeightProjectorExact as Weight
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorExact as Point
import DASHI.Moonshine.Monster3BFiniteX6ConstructiveComparisonExact as Compare
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact as Extract

booleanDelta : H.X6 → V.SchrodingerFunction
booleanDelta selected x with V.x6Equal selected x
... | true = C3.one
... | false = C3.zero

------------------------------------------------------------------------
-- Coordinate-difference witnesses force the complete Boolean equality false.
------------------------------------------------------------------------

andRightFalse : (b : Bool) → V._and_ b false ≡ false
andRightFalse false = refl
andRightFalse true = refl

and2RightFalse : (a b : Bool) → V._and_ a (V._and_ b false) ≡ false
and2RightFalse false b = refl
and2RightFalse true b = andRightFalse b

and3RightFalse : (a b c : Bool) →
  V._and_ a (V._and_ b (V._and_ c false)) ≡ false
and3RightFalse false b c = refl
and3RightFalse true b c = and2RightFalse b c

and4RightFalse : (a b c d : Bool) →
  V._and_ a (V._and_ b (V._and_ c (V._and_ d false))) ≡ false
and4RightFalse false b c d = refl
and4RightFalse true b c d = and3RightFalse b c d

and5RightFalse : (a b c d e : Bool) →
  V._and_ a (V._and_ b (V._and_ c (V._and_ d (V._and_ e false)))) ≡ false
and5RightFalse false b c d e = refl
and5RightFalse true b c d e = and4RightFalse b c d e

coordinateDifferenceForcesBooleanFalse :
  ∀ {selected x} →
  Point.CoordinateDifference selected x →
  V.x6Equal selected x ≡ false
coordinateDifferenceForcesBooleanFalse {selected = H.x6 s0 s1 s2 s3 s4 s5}
  {x = H.x6 x0 x1 x2 x3 x4 x5} (Point.differs0 d0)
  rewrite d0 = refl
coordinateDifferenceForcesBooleanFalse {selected = H.x6 s0 s1 s2 s3 s4 s5}
  {x = H.x6 x0 x1 x2 x3 x4 x5} (Point.differs1 d1)
  rewrite d1 = andRightFalse (V.tritEqual s0 x0)
coordinateDifferenceForcesBooleanFalse {selected = H.x6 s0 s1 s2 s3 s4 s5}
  {x = H.x6 x0 x1 x2 x3 x4 x5} (Point.differs2 d2)
  rewrite d2 = and2RightFalse (V.tritEqual s0 x0) (V.tritEqual s1 x1)
coordinateDifferenceForcesBooleanFalse {selected = H.x6 s0 s1 s2 s3 s4 s5}
  {x = H.x6 x0 x1 x2 x3 x4 x5} (Point.differs3 d3)
  rewrite d3 = and3RightFalse (V.tritEqual s0 x0) (V.tritEqual s1 x1)
    (V.tritEqual s2 x2)
coordinateDifferenceForcesBooleanFalse {selected = H.x6 s0 s1 s2 s3 s4 s5}
  {x = H.x6 x0 x1 x2 x3 x4 x5} (Point.differs4 d4)
  rewrite d4 = and4RightFalse (V.tritEqual s0 x0) (V.tritEqual s1 x1)
    (V.tritEqual s2 x2) (V.tritEqual s3 x3)
coordinateDifferenceForcesBooleanFalse {selected = H.x6 s0 s1 s2 s3 s4 s5}
  {x = H.x6 x0 x1 x2 x3 x4 x5} (Point.differs5 d5)
  rewrite d5 = and5RightFalse (V.tritEqual s0 x0) (V.tritEqual s1 x1)
    (V.tritEqual s2 x2) (V.tritEqual s3 x3) (V.tritEqual s4 x4)

------------------------------------------------------------------------
-- Comparison delta and Boolean delta are pointwise identical.
------------------------------------------------------------------------

comparisonDeltaIsBooleanDelta :
  (selected : H.X6) →
  V.PointwiseEqual (Extract.comparisonDelta selected) (booleanDelta selected)
comparisonDeltaIsBooleanDelta selected x with Compare.compareX6 selected x
... | Compare.sameX6 refl rewrite Compare.x6EqualRefl selected = refl
... | Compare.differentX6 difference
  rewrite coordinateDifferenceForcesBooleanFalse difference = refl

booleanDeltaMemberFromExtraction :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    (witness : Extract.NonzeroInvariantVector inv) →
  Member (booleanDelta (Extract.selected witness))
booleanDeltaMemberFromExtraction inv witness =
  V.closedUnderPointwiseEquality inv
    (Extract.comparisonDelta (Extract.selected witness))
    (booleanDelta (Extract.selected witness))
    (Extract.deltaLineMember inv witness)
    (comparisonDeltaIsBooleanDelta (Extract.selected witness))

------------------------------------------------------------------------
-- V.x6Equal and the older projector equality are definitionally the same
-- six-coordinate Boolean test, so reuse the already-proved covariance theorem.
------------------------------------------------------------------------

x6EqualTranslationCovariant :
  (axis : H.Axis6) (left right : H.X6) →
  V.x6Equal (H.translate axis left) (H.translate axis right)
  ≡ V.x6Equal left right
x6EqualTranslationCovariant = Weight.x6EqualTranslationCovariant

unitTranslationCarriesBooleanDeltaPointwise :
  (axis : H.Axis6) (selected : H.X6) →
  V.PointwiseEqual
    (V.translationAction axis (booleanDelta selected))
    (booleanDelta (H.translate axis selected))
unitTranslationCarriesBooleanDeltaPointwise axis selected x =
  let
    inverseX = H.translateInverse axis x
    cov = x6EqualTranslationCovariant axis selected inverseX
    restore = Perm.translateAfterTranslateInverse axis x
  in
  -- Both functions branch only on the displayed Boolean equality.  Rewrite
  -- the target equality back to the source/inverse equality.
  trans
    refl
    (helper axis selected x cov restore)
  where
  helper :
    (axis : H.Axis6) (selected x : H.X6) →
    V.x6Equal (H.translate axis selected)
      (H.translate axis (H.translateInverse axis x))
      ≡ V.x6Equal selected (H.translateInverse axis x) →
    H.translate axis (H.translateInverse axis x) ≡ x →
    booleanDelta selected (H.translateInverse axis x)
      ≡ booleanDelta (H.translate axis selected) x
  helper axis selected x cov restore
    rewrite sym restore | cov
    with V.x6Equal selected (H.translateInverse axis x)
  ... | true = refl
  ... | false = refl

record BooleanDeltaBoundary : Set where
  constructor boolean-delta-boundary
  field
    comparisonAndBooleanDeltaPointwiseEqual : Bool
    extractedDeltaTransfersToBooleanDelta : Bool
    unitTranslationCovarianceProved : Bool
    arbitraryPermutationClosureUsed : Bool
open BooleanDeltaBoundary public

canonicalBooleanDeltaBoundary : BooleanDeltaBoundary
canonicalBooleanDeltaBoundary =
  boolean-delta-boundary true true true false
