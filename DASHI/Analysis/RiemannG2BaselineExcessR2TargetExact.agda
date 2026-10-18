module DASHI.Analysis.RiemannG2BaselineExcessR2TargetExact where

------------------------------------------------------------------------
-- CONSUMER-FAITHFUL R2 TARGET AFTER RECOVERING THE 8889 THEOREM BYTES
--
-- The actual cluster theorem is naturally centered at a shared positive
-- baseline.  For horizontal displacement a = Re(rho)-1/2 it supplies a surplus
--
--   M(a,g) = (sqrt(2)/2) * a^2 * secondMoment(g)
--
-- above baselineCluster.
--
-- Hence the high-side acquisition problem should be organized as
--
--   B_comp <= baselineCluster + E_comp
--   E_comp < M(a,g)
--   baselineCluster + M(a,g) <= ClusterResponse.
--
-- The last line is theorem-bearing in vendored Lean source.  The first two
-- contain the remaining sharp Off/Gamma mathematics.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record BaselineExcessR2Target : Set₁ where
  field
    Scalar : Set
    _≤_ _<_ : Scalar → Scalar → Set
    add mul : Scalar → Scalar → Scalar

    complementBudget : Scalar
    baselineCluster : Scalar
    complementExcess : Scalar
    clusterMargin : Scalar
    actualClusterResponse : Scalar

    complementBudgetBelowBaselinePlusExcess :
      _≤_ complementBudget (add baselineCluster complementExcess)

    excessStrictBelowClusterMargin :
      _<_ complementExcess clusterMargin

    baselinePlusMarginBelowActualCluster :
      _≤_ (add baselineCluster clusterMargin) actualClusterResponse

    sameScalarOrderAsFinalR2 : Set
    sameScalarOrderAsFinalR2Receipt : sameScalarOrderAsFinalR2

    targetReference : String

open BaselineExcessR2Target public

record BaselineExcessR2Boundary : Set where
  constructor baseline-excess-r2-boundary
  field
    absoluteClusterInverseSquareCoefficientPrimitive : Bool
    sharedBaselinePrimitive : Bool
    horizontalSquareClusterMarginPrimitive : Bool
    fixedQuarticFarCutoffUniformInOffLineDisplacement : Bool
    displacementAdaptiveCutoffRequired : Bool
    vendoredClusterLowerTheoremAvailableForTransport : Bool
    sharpComplementExcessStillAnalytic : Bool
    r2DerivedHere : Bool

open BaselineExcessR2Boundary public

canonicalBaselineExcessR2Boundary : BaselineExcessR2Boundary
canonicalBaselineExcessR2Boundary =
  baseline-excess-r2-boundary
    false
    true
    true
    false
    true
    true
    true
    false
