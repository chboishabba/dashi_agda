module DASHI.Analysis.BishopOriginalFiniteMeshPositiveGapExact where

------------------------------------------------------------------------
-- K04d P0.04: ORIGINAL FINITE MESH GAP / RECIPROCAL WITNESSES.
--
-- For every actual finiteWalk vertex with 0<=v_j<1, construct
-- the existing BishopUnitIntervalRatio, strictly positive gap
-- w_j=1-v_j, nonzero receipt, positive inverse and cancellation.
--
-- This is the *actual pinned* Bishop inverse. A uniform quantitative
-- upper bound inverse(w_j)<=inverse(1-r) still needs the source
-- antitone inverse theorem and the common v_j<=r hypothesis.
--
-- Source: Bishop/Bridges; Murray/Csimma pinned Real/Inverse;
-- DASHI original geometric gap and finite-walk owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as RP
import Inverse as Inv

import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap

originalBishopMeshVertexRatio :
  (steps : Nat → R.ℝ) (n : Nat) →
  R._≤_ R.0ℝ (Mesh.sourceVertex steps n) →
  R._<_ (Mesh.sourceVertex steps n) R.1ℝ →
  Gap.BishopUnitIntervalRatio (Mesh.sourceVertex steps n)
originalBishopMeshVertexRatio steps n nonnegative belowOne = record
  { ratioNonnegative = nonnegative
  ; ratioBelowOne = belowOne
  }

originalBishopMeshWeightsPositive :
  (steps : Nat → R.ℝ) (n : Nat) →
  (nonnegative : R._≤_ R.0ℝ (Mesh.sourceVertex steps n)) →
  (belowOne : R._<_ (Mesh.sourceVertex steps n) R.1ℝ) →
  R._<_ R.0ℝ
    (Cross.oneMinus (Mesh.sourceVertex steps n))
originalBishopMeshWeightsPositive steps n nonnegative belowOne =
  Gap.oneMinusPositive
    (originalBishopMeshVertexRatio
      steps n nonnegative belowOne)

originalBishopMeshWeightNonzero :
  (steps : Nat → R.ℝ) (n : Nat) →
  (nonnegative : R._≤_ R.0ℝ (Mesh.sourceVertex steps n)) →
  (belowOne : R._<_ (Mesh.sourceVertex steps n) R.1ℝ) →
  R._≄0 (Cross.oneMinus (Mesh.sourceVertex steps n))
originalBishopMeshWeightNonzero steps n nonnegative belowOne =
  Gap.oneMinusNonzero
    (originalBishopMeshVertexRatio
      steps n nonnegative belowOne)

originalBishopMeshWeightInverse :
  (steps : Nat → R.ℝ) (n : Nat) →
  (nonnegative : R._≤_ R.0ℝ (Mesh.sourceVertex steps n)) →
  (belowOne : R._<_ (Mesh.sourceVertex steps n) R.1ℝ) →
  R.ℝ
originalBishopMeshWeightInverse steps n nonnegative belowOne =
  Gap.oneMinusInverse
    (originalBishopMeshVertexRatio
      steps n nonnegative belowOne)

originalBishopMeshWeightInversePositive :
  (steps : Nat → R.ℝ) (n : Nat) →
  (nonnegative : R._≤_ R.0ℝ (Mesh.sourceVertex steps n)) →
  (belowOne : R._<_ (Mesh.sourceVertex steps n) R.1ℝ) →
  R._<_ R.0ℝ
    (originalBishopMeshWeightInverse
      steps n nonnegative belowOne)
originalBishopMeshWeightInversePositive steps n nonnegative belowOne =
  Inv.0<x⇒0<x⁻¹
    (originalBishopMeshWeightNonzero
      steps n nonnegative belowOne)
    (originalBishopMeshWeightsPositive
      steps n nonnegative belowOne)

originalBishopMeshWeightInverseCancels :
  (steps : Nat → R.ℝ) (n : Nat) →
  (nonnegative : R._≤_ R.0ℝ (Mesh.sourceVertex steps n)) →
  (belowOne : R._<_ (Mesh.sourceVertex steps n) R.1ℝ) →
  R._≃_
    (R._*_
      (originalBishopMeshWeightInverse
        steps n nonnegative belowOne)
      (Cross.oneMinus (Mesh.sourceVertex steps n)))
    R.1ℝ
originalBishopMeshWeightInverseCancels steps n nonnegative belowOne =
  Inv.*-inverseˡ
    (Cross.oneMinus (Mesh.sourceVertex steps n))
    (originalBishopMeshWeightNonzero
      steps n nonnegative belowOne)
