module DASHI.Physics.Closure.NSTriadKNHHGoodResidualShellTransportRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- DASHI CONTRIBUTION
--
-- The Round-38 quotient theorem says the physically relevant HH-good source
-- variable is the line residual
--
--   delta_v(w) = w x v,
--
-- not |w| after an early absolute-value estimate.  This module proves that the
-- residual can be transported *exactly* through finite linear shell/kernel
-- decompositions:
--
--   delta_v(w1+w2) = delta_v(w1)+delta_v(w2),
--   delta_v(a w)   = a delta_v(w),
--   delta_v(sum_i a_i w_i) = sum_i a_i delta_v(w_i).
--
-- Consequently the cross-product receipt can survive shell decomposition and
-- PV cancellation all the way to the final analytic absorption estimate.  No
-- Cauchy--Schwarz replacement |w x v| <= |w||v| is performed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNVorticityLineResidualRound38Exact as Residual

zeroVector : V.Vector3
zeroVector = V.v3 0ℚ 0ℚ 0ℚ

lineResidualAdditive : ∀ target left right →
  Residual.lineResidual target (V.add left right)
  ≡ V.add
      (Residual.lineResidual target left)
      (Residual.lineResidual target right)
lineResidualAdditive
    (V.v3 tx ty tz)
    (V.v3 lx ly lz)
    (V.v3 rx ry rz) =
  V.vectorExt
    (solve (tx ∷ ty ∷ tz ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ []))

lineResidualHomogeneous : ∀ scalar target source →
  Residual.lineResidual target (V.scale scalar source)
  ≡ V.scale scalar (Residual.lineResidual target source)
lineResidualHomogeneous scalar
    (V.v3 tx ty tz)
    (V.v3 sx sy sz) =
  V.vectorExt
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ sx ∷ sy ∷ sz ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ sx ∷ sy ∷ sz ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ sx ∷ sy ∷ sz ∷ []))

lineResidualZero : ∀ target →
  Residual.lineResidual target zeroVector ≡ zeroVector
lineResidualZero (V.v3 tx ty tz) =
  V.vectorExt
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))

record WeightedSourceSample : Set where
  constructor weighted-source-sample
  field
    weight : ℚ
    source : V.Vector3

open WeightedSourceSample public

weightedSource : WeightedSourceSample → V.Vector3
weightedSource sample = V.scale (weight sample) (source sample)

weightedSourceSum : List WeightedSourceSample → V.Vector3
weightedSourceSum [] = zeroVector
weightedSourceSum (sample ∷ rest) =
  V.add (weightedSource sample) (weightedSourceSum rest)

weightedResidual : V.Vector3 → WeightedSourceSample → V.Vector3
weightedResidual target sample =
  V.scale (weight sample) (Residual.lineResidual target (source sample))

weightedResidualSum :
  V.Vector3 → List WeightedSourceSample → V.Vector3
weightedResidualSum target [] = zeroVector
weightedResidualSum target (sample ∷ rest) =
  V.add (weightedResidual target sample) (weightedResidualSum target rest)

lineResidualCommutesWithFiniteWeightedShellSum :
  ∀ target samples →
  Residual.lineResidual target (weightedSourceSum samples)
  ≡ weightedResidualSum target samples
lineResidualCommutesWithFiniteWeightedShellSum target [] =
  lineResidualZero target
lineResidualCommutesWithFiniteWeightedShellSum target (sample ∷ rest) =
  trans
    (lineResidualAdditive target
      (weightedSource sample)
      (weightedSourceSum rest))
    (trans
      (cong
        (λ first →
          V.add first
            (Residual.lineResidual target (weightedSourceSum rest)))
        (lineResidualHomogeneous
          (weight sample) target (source sample)))
      (cong
        (V.add (weightedResidual target sample))
        (lineResidualCommutesWithFiniteWeightedShellSum target rest)))

record WeightedParallelPerturbation : Set where
  constructor weighted-parallel-perturbation
  field
    coefficient : ℚ

open WeightedParallelPerturbation public

addParallelPerturbation :
  V.Vector3 → WeightedParallelPerturbation →
  WeightedSourceSample → WeightedSourceSample
addParallelPerturbation target perturbation sample =
  weighted-source-sample
    (weight sample)
    (Residual.parallelShift
      (coefficient perturbation) target (source sample))

weightedResidualIgnoresParallelPerturbation :
  ∀ target perturbation sample →
  weightedResidual target (addParallelPerturbation target perturbation sample)
  ≡ weightedResidual target sample
weightedResidualIgnoresParallelPerturbation target perturbation sample =
  cong
    (V.scale (weight sample))
    (Residual.lineResidualIgnoresParallelComponent
      (coefficient perturbation) target (source sample))

hhGoodResidualFiniteShellTransportClosed : Bool
hhGoodResidualFiniteShellTransportClosed = true

physicalPVResidualPreservingShellDecompositionConstructed : Bool
physicalPVResidualPreservingShellDecompositionConstructed = false

hhGoodResidualFiniteShellTransportClosedIsTrue :
  hhGoodResidualFiniteShellTransportClosed ≡ true
hhGoodResidualFiniteShellTransportClosedIsTrue = refl
