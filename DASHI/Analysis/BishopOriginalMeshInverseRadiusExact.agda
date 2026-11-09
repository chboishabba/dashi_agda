module DASHI.Analysis.BishopOriginalMeshInverseRadiusExact where

------------------------------------------------------------------------
-- P0.04 / first terminal cut: a COMMON NATIVE BISHOP reciprocal
-- upper bound for every original finite-mesh vertex.
--
-- For vertices 0 <= v_j <= R < 1, put rho=(R+1)/2, so
-- R < rho < 1. Then
--
--  0 < inv_B(1-v_j) < inv_B(1-rho).
--
-- Using rho rather than R is essential because the pinned Bishop
-- reciprocal-order theorem is STRICT, and v_j can equal R.
-- The larger radius is the already constructed original Bishop
-- unit-interval midpoint; not an independent selected constant.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as RP
import Inverse as Inv

import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopUnitIntervalMidpointExact as Mid
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap

originalBishopGapStrictAntitone :
  (vertex radius : R.ℝ) →
  R._<_ vertex radius →
  R._<_
    (Cross.oneMinus radius)
    (Cross.oneMinus vertex)
originalBishopGapStrictAntitone vertex radius below =
  RP.+-monoʳ-< R.1ℝ (RP.neg-mono-< below)

originalBishopInverseStrictAntitone :
  (vertex radius : R.ℝ) →
  (vertexRatio : Gap.BishopUnitIntervalRatio vertex) →
  (radiusRatio : Gap.BishopUnitIntervalRatio radius) →
  R._<_ vertex radius →
  R._<_
    (Gap.oneMinusInverse vertexRatio)
    (Gap.oneMinusInverse radiusRatio)
originalBishopInverseStrictAntitone
    vertex radius vertexRatio radiusRatio below =
  Inv.x<y∧posx,y⇒y⁻¹<x⁻¹
    (originalBishopGapStrictAntitone vertex radius below)
    (Gap.oneMinusNonzero radiusRatio)
    (Gap.oneMinusNonzero vertexRatio)
    (RP.0<x⇒posx (Gap.oneMinusPositive radiusRatio))
    (RP.0<x⇒posx (Gap.oneMinusPositive vertexRatio))

originalBishopMidpointRadiusRatio :
  (radius : R.ℝ) →
  Gap.BishopUnitIntervalRatio radius →
  Gap.BishopUnitIntervalRatio (Mid.midpointToOne radius)
originalBishopMidpointRadiusRatio radius radiusRatio = record
  { ratioNonnegative =
      RP.<⇒≤
        (RP.≤-<-trans
          (Gap.ratioNonnegative radiusRatio)
          (Mid.ratioBelowMidpoint radiusRatio))
  ; ratioBelowOne = Mid.midpointBelowOne radiusRatio
  }

originalBishopMeshInverseDominatedByRadiusInverse :
  (steps : Nat → R.ℝ) (j : Nat) (radius : R.ℝ) →
  (vertexRatio :
    Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps j)) →
  (radiusRatio : Gap.BishopUnitIntervalRatio radius) →
  R._≤_ (Mesh.sourceVertex steps j) radius →
  R._≤_
    (Gap.oneMinusInverse vertexRatio)
    (Gap.oneMinusInverse
      (originalBishopMidpointRadiusRatio radius radiusRatio))
originalBishopMeshInverseDominatedByRadiusInverse
    steps j radius vertexRatio radiusRatio inside =
  RP.<⇒≤
    (originalBishopInverseStrictAntitone
      (Mesh.sourceVertex steps j)
      (Mid.midpointToOne radius)
      vertexRatio
      (originalBishopMidpointRadiusRatio radius radiusRatio)
      (RP.≤-<-trans inside
        (Mid.ratioBelowMidpoint radiusRatio)))
