module DASHI.Analysis.BishopOriginalClippedEqualMeshExact where

------------------------------------------------------------------------
-- K04d P0.06: CONCRETE REFINING EQUAL-STEP ORIGINAL BISHOP MESH.
--
-- Given 0<=x<1 and count n, choose h=x/(n+1) from the ORIGINAL
-- Nat reciprocal. Define the Nat-indexed step sequence:
--
--   h_j = h for 0<=j<n+1; h_j=0 afterwards.
--
-- Unlike an endlessly repeated positive step, this really satisfies
-- the GLOBAL source mesh invariant 0<=v_j<=x for every j, and
-- v_(n+1)=x exactly. The stage/count is not a synthetic grid carrier.
--
-- This pays finite endpoint identity, positivity, clipping and
-- all-index radius receipts for the P0.05/P0.06 source theorems.
-- Separate convergence of the mesh defect budget is still needed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as Scale
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap

sourceClippedConstantSteps :
  (cells : Nat) (step : R.ℝ) → Nat → R.ℝ
sourceClippedConstantSteps zero step j = R.0ℝ
sourceClippedConstantSteps (suc count) step zero = step
sourceClippedConstantSteps (suc count) step (suc j) =
  sourceClippedConstantSteps count step j

originalClippedZeroMeshIsZero :
  (step : R.ℝ) (j : Nat) →
  R._≃_
    (Mesh.sourceVertex (sourceClippedConstantSteps zero step) j)
    R.0ℝ
originalClippedZeroMeshIsZero step zero = RP.≃-refl
originalClippedZeroMeshIsZero step (suc j) =
  RP.≃-trans
    (RP.+-cong
      (originalClippedZeroMeshIsZero step j)
      RP.≃-refl)
    (RP.+-identityʳ R.0ℝ)

originalClippedMeshShift :
  (step : R.ℝ) (count j : Nat) →
  R._≃_
    (Mesh.sourceVertex
      (sourceClippedConstantSteps (suc count) step) (suc j))
    (R._+_ step
      (Mesh.sourceVertex
        (sourceClippedConstantSteps count step) j))
originalClippedMeshShift step count zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ hh → Κ 0ℚᵘ ⊕ hh ⊜ hh ⊕ Κ 0ℚᵘ)
    RP.≃-refl step
originalClippedMeshShift step count (suc j) =
  let
    inner = Mesh.sourceVertex
      (sourceClippedConstantSteps count step) j
    next = sourceClippedConstantSteps count step j
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (originalClippedMeshShift step count j)
      RP.≃-refl)
    (solve 3
      (λ hh xx yy →
        (hh ⊕ xx) ⊕ yy
        ⊜ hh ⊕ (xx ⊕ yy))
      RP.≃-refl step inner next)

originalClippedMeshEndpointIsNatScale :
  (step : R.ℝ) (cells : Nat) →
  R._≃_
    (Mesh.sourceVertex (sourceClippedConstantSteps cells step) cells)
    (Power.natScale cells step)
originalClippedMeshEndpointIsNatScale step zero = RP.≃-refl
originalClippedMeshEndpointIsNatScale step (suc cells) =
  RP.≃-trans
    (originalClippedMeshShift step cells cells)
    (RP.≃-trans
      (RP.+-cong RP.≃-refl
        (originalClippedMeshEndpointIsNatScale step cells))
      (RP.+-comm step (Power.natScale cells step)))

originalNatScaleNonnegative :
  (step : R.ℝ) →
  R.NonNegative step →
  (cells : Nat) →
  R.NonNegative (Power.natScale cells step)
originalNatScaleNonnegative step stepNN zero = RP.nonNeg0
originalNatScaleNonnegative step stepNN (suc count) =
  RP.nonNegx,y⇒nonNegx+y
    (originalNatScaleNonnegative step stepNN count)
    stepNN

originalClippedMeshStepNonnegative :
  (step : R.ℝ) →
  R.NonNegative step →
  (count j : Nat) →
  R.NonNegative (sourceClippedConstantSteps count step j)
originalClippedMeshStepNonnegative step stepNN zero j = RP.nonNeg0
originalClippedMeshStepNonnegative step stepNN (suc count) zero = stepNN
originalClippedMeshStepNonnegative step stepNN (suc count) (suc j) =
  originalClippedMeshStepNonnegative step stepNN count j

originalClippedMeshVertexNonnegative :
  (step : R.ℝ) →
  R.NonNegative step →
  (count j : Nat) →
  R.NonNegative
    (Mesh.sourceVertex (sourceClippedConstantSteps count step) j)
originalClippedMeshVertexNonnegative step stepNN count zero =
  RP.nonNeg0
originalClippedMeshVertexNonnegative step stepNN count (suc j) =
  RP.nonNegx,y⇒nonNegx+y
    (originalClippedMeshVertexNonnegative step stepNN count j)
    (originalClippedMeshStepNonnegative step stepNN count j)

originalClippedMeshVertexBelowEndpoint :
  (step : R.ℝ) →
  (stepNN : R.NonNegative step) →
  (count j : Nat) →
  R._≤_
    (Mesh.sourceVertex (sourceClippedConstantSteps count step) j)
    (Power.natScale count step)
originalClippedMeshVertexBelowEndpoint step stepNN zero j =
  RP.≤-respˡ-≃
    (originalClippedZeroMeshIsZero step j)
    RP.≤-refl
originalClippedMeshVertexBelowEndpoint
    step stepNN (suc count) zero =
  RP.nonNegx⇒0≤x
    (originalNatScaleNonnegative step stepNN (suc count))
originalClippedMeshVertexBelowEndpoint
    step stepNN (suc count) (suc j) =
  let
    old = Mesh.sourceVertex (sourceClippedConstantSteps count step) j
    bound = RP.+-monoʳ-≤ step
      (originalClippedMeshVertexBelowEndpoint step stepNN count j)
    shifted =
      RP.≤-respʳ-≃
        (RP.+-comm step (Power.natScale count step))
        bound
  in
  RP.≤-respˡ-≃
    (originalClippedMeshShift step count j)
    shifted

sourceEqualStep :
  (x : R.ℝ) (n : Nat) → R.ℝ
sourceEqualStep x n =
  R._*_ x (R._⋆ (Recip.reciprocalNatRational n))

sourceClippedEqualSteps :
  (x : R.ℝ) (n : Nat) → Nat → R.ℝ
sourceClippedEqualSteps x n =
  sourceClippedConstantSteps (suc n) (sourceEqualStep x n)

originalClippedEqualMeshEndpointIsX :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (Mesh.sourceVertex (sourceClippedEqualSteps x n) (suc n))
    x
originalClippedEqualMeshEndpointIsX x n =
  let
    h = sourceEqualStep x n
    count = NatReal.natReal (suc n)
    recip = R._⋆ (Recip.reciprocalNatRational n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (originalClippedMeshEndpointIsNatScale h (suc n))
    (RP.≃-trans
      (Scale.recursiveScaleIsEmbeddedNaturalMultiply (suc n) h)
      (RP.≃-trans
        (solve 3
          (λ cc xx rr →
            cc ⊗ (xx ⊗ rr)
            ⊜ xx ⊗ (rr ⊗ cc))
          RP.≃-refl count x recip)
        (RP.≃-trans
          (RP.*-cong RP.≃-refl
            (Recip.embeddedReciprocalNatCancels n))
          (RP.*-identityʳ x))))

originalClippedEqualMeshStepNonnegative :
  (x : R.ℝ) (n : Nat) →
  (xNN : R.NonNegative x) →
  (j : Nat) →
  R.NonNegative (sourceClippedEqualSteps x n j)
originalClippedEqualMeshStepNonnegative x n xNN j =
  originalClippedMeshStepNonnegative
    (sourceEqualStep x n)
    (RP.nonNegx,y⇒nonNegx*y
      xNN (Recip.reciprocalNonnegative n))
    (suc n) j

originalClippedEqualMeshVertexNonnegative :
  (x : R.ℝ) (n : Nat) →
  (xNN : R.NonNegative x) →
  (j : Nat) →
  R.NonNegative
    (Mesh.sourceVertex (sourceClippedEqualSteps x n) j)
originalClippedEqualMeshVertexNonnegative x n xNN j =
  originalClippedMeshVertexNonnegative
    (sourceEqualStep x n)
    (RP.nonNegx,y⇒nonNegx*y
      xNN (Recip.reciprocalNonnegative n))
    (suc n) j

originalClippedEqualMeshVertexBelowX :
  (x : R.ℝ) (n : Nat) →
  (xNN : R.NonNegative x) →
  (j : Nat) →
  R._≤_
    (Mesh.sourceVertex (sourceClippedEqualSteps x n) j)
    x
originalClippedEqualMeshVertexBelowX x n xNN j =
  RP.≤-respʳ-≃
    (originalClippedEqualMeshEndpointIsX x n)
    (originalClippedMeshVertexBelowEndpoint
      (sourceEqualStep x n)
      (RP.nonNegx,y⇒nonNegx*y
        xNN (Recip.reciprocalNonnegative n))
      (suc n) j)

originalClippedEqualMeshVertexRatio :
  (x : R.ℝ) (n : Nat) →
  (ratio : Gap.BishopUnitIntervalRatio x) →
  (j : Nat) →
  Gap.BishopUnitIntervalRatio
    (Mesh.sourceVertex (sourceClippedEqualSteps x n) j)
originalClippedEqualMeshVertexRatio x n ratio j = record
  { ratioNonnegative =
      RP.nonNegx⇒0≤x
        (originalClippedEqualMeshVertexNonnegative
          x n (Gap.ratioNonnegativeWitness ratio) j)
  ; ratioBelowOne =
      RP.≤-<-trans
        (originalClippedEqualMeshVertexBelowX
          x n (Gap.ratioNonnegativeWitness ratio) j)
        (Gap.ratioBelowOne ratio)
  }
