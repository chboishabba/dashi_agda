module DASHI.Physics.Closure.NSTriadKNHHGoodPVResidualOrderRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- DASHI CONTRIBUTION
--
-- Make the required order of the HH-good argument exact on the finite shell/PV
-- carrier.  For weighted vector samples, zero kernel mass kills an arbitrary
-- constant source *before* taking the vorticity-line residual.  Linearity then
-- transports the residual through the already-cancelled weighted sum:
--
--   sum w_i = 0
--     => sum w_i (s_i + c) = sum w_i s_i
--     => delta_v(sum w_i (s_i+c))
--          = sum w_i delta_v(s_i).
--
-- Thus there is no mathematical need to estimate |s_i| before principal-value
-- cancellation.  The cross-product residual can remain intact until the final
-- directional-threshold/Young absorption step.  This is the finite exact audit
-- invariant for the physical singular-near proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNVorticityLineResidualRound38Exact as Residual
import DASHI.Physics.Closure.NSTriadKNHHGoodResidualShellTransportRound39Exact as Shell

sumWeights : List Shell.WeightedSourceSample → ℚ
sumWeights [] = 0ℚ
sumWeights (sample ∷ rest) = Shell.weight sample + sumWeights rest

record ZeroMassWeightedSources
    (samples : List Shell.WeightedSourceSample) : Set where
  field
    totalWeightZero : sumWeights samples ≡ 0ℚ

open ZeroMassWeightedSources public

shiftSourceByConstant :
  V.Vector3 → Shell.WeightedSourceSample → Shell.WeightedSourceSample
shiftSourceByConstant constant sample =
  Shell.weighted-source-sample
    (Shell.weight sample)
    (V.add (Shell.source sample) constant)

mapConstantShift :
  V.Vector3 → List Shell.WeightedSourceSample →
  List Shell.WeightedSourceSample
mapConstantShift constant [] = []
mapConstantShift constant (sample ∷ rest) =
  shiftSourceByConstant constant sample ∷ mapConstantShift constant rest

weightedConstant : ℚ → V.Vector3 → V.Vector3
weightedConstant weight constant = V.scale weight constant

weightedSourceShiftMeaning :
  ∀ constant sample →
  Shell.weightedSource (shiftSourceByConstant constant sample)
  ≡ V.add
      (Shell.weightedSource sample)
      (weightedConstant (Shell.weight sample) constant)
weightedSourceShiftMeaning
    (V.v3 cx cy cz)
    (Shell.weighted-source-sample weight (V.v3 sx sy sz)) =
  V.vectorExt
    (solve (weight ∷ sx ∷ sy ∷ sz ∷ cx ∷ cy ∷ cz ∷ []))
    (solve (weight ∷ sx ∷ sy ∷ sz ∷ cx ∷ cy ∷ cz ∷ []))
    (solve (weight ∷ sx ∷ sy ∷ sz ∷ cx ∷ cy ∷ cz ∷ []))

weightedConstantSum :
  V.Vector3 → List Shell.WeightedSourceSample → V.Vector3
weightedConstantSum constant samples =
  weightedConstant (sumWeights samples) constant

weightedSourceSumShiftDecomposition :
  ∀ constant samples →
  Shell.weightedSourceSum (mapConstantShift constant samples)
  ≡ V.add
      (Shell.weightedSourceSum samples)
      (weightedConstantSum constant samples)
weightedSourceSumShiftDecomposition constant [] =
  V.vectorExt refl refl refl
weightedSourceSumShiftDecomposition
    constant (sample ∷ rest) =
  trans
    (cong
      (λ first → V.add first
        (Shell.weightedSourceSum (mapConstantShift constant rest)))
      (weightedSourceShiftMeaning constant sample))
    (trans
      (cong
        (V.add
          (V.add
            (Shell.weightedSource sample)
            (weightedConstant (Shell.weight sample) constant)))
        (weightedSourceSumShiftDecomposition constant rest))
      (vectorReassociateAndCollect
        (Shell.weightedSource sample)
        (Shell.weightedSourceSum rest)
        (Shell.weight sample)
        (sumWeights rest)
        constant))
  where
  vectorReassociateAndCollect :
    ∀ left right a b c →
    V.add
      (V.add left (V.scale a c))
      (V.add right (V.scale b c))
    ≡
    V.add
      (V.add left right)
      (V.scale (a + b) c)
  vectorReassociateAndCollect
      (V.v3 lx ly lz) (V.v3 rx ry rz)
      a b (V.v3 cx cy cz) =
    V.vectorExt
      (solve (lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ a ∷ b ∷ cx ∷ cy ∷ cz ∷ []))
      (solve (lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ a ∷ b ∷ cx ∷ cy ∷ cz ∷ []))
      (solve (lx ∷ ly ∷ lz ∷ rx ∷ ry ∷ rz ∷ a ∷ b ∷ cx ∷ cy ∷ cz ∷ []))

zeroMassKillsConstantShift :
  ∀ constant samples →
  ZeroMassWeightedSources samples →
  Shell.weightedSourceSum (mapConstantShift constant samples)
  ≡ Shell.weightedSourceSum samples
zeroMassKillsConstantShift constant samples zeroMass =
  trans
    (weightedSourceSumShiftDecomposition constant samples)
    (trans
      (cong
        (λ mass →
          V.add (Shell.weightedSourceSum samples)
            (V.scale mass constant))
        (totalWeightZero zeroMass))
      (vectorAddScaledZeroRight (Shell.weightedSourceSum samples) constant))
  where
  vectorAddScaledZeroRight : ∀ value constant →
    V.add value (V.scale 0ℚ constant) ≡ value
  vectorAddScaledZeroRight
      (V.v3 vx vy vz) (V.v3 cx cy cz) =
    V.vectorExt
      (solve (vx ∷ cx ∷ []))
      (solve (vy ∷ cy ∷ []))
      (solve (vz ∷ cz ∷ []))

pvCancellationThenResidual :
  ∀ target constant samples →
  ZeroMassWeightedSources samples →
  Residual.lineResidual target
    (Shell.weightedSourceSum (mapConstantShift constant samples))
  ≡ Shell.weightedResidualSum target samples
pvCancellationThenResidual target constant samples zeroMass =
  trans
    (cong (Residual.lineResidual target)
      (zeroMassKillsConstantShift constant samples zeroMass))
    (Shell.lineResidualCommutesWithFiniteWeightedShellSum target samples)

parallelConstantIsInvisibleEvenBeforeMassCancellation :
  ∀ target scalar samples →
  Shell.weightedResidualSum target
    (mapConstantShift (V.scale scalar target) samples)
  ≡ Shell.weightedResidualSum target samples
parallelConstantIsInvisibleEvenBeforeMassCancellation target scalar [] = refl
parallelConstantIsInvisibleEvenBeforeMassCancellation
    target scalar (sample ∷ rest) =
  trans
    (cong
      (λ first → V.add first
        (Shell.weightedResidualSum target
          (mapConstantShift (V.scale scalar target) rest)))
      (weightedResidualShiftParallel target scalar sample))
    (cong
      (V.add (Shell.weightedResidual target sample))
      (parallelConstantIsInvisibleEvenBeforeMassCancellation
        target scalar rest))
  where
  weightedResidualShiftParallel : ∀ target scalar sample →
    Shell.weightedResidual target
      (shiftSourceByConstant (V.scale scalar target) sample)
    ≡ Shell.weightedResidual target sample
  weightedResidualShiftParallel target scalar sample =
    cong
      (V.scale (Shell.weight sample))
      (Residual.lineResidualIgnoresParallelComponent
        scalar target (Shell.source sample))

hhGoodPVCancellationBeforeScalarizationClosed : Bool
hhGoodPVCancellationBeforeScalarizationClosed = true

physicalHHGoodSingularNearShellTimeBoundConstructed : Bool
physicalHHGoodSingularNearShellTimeBoundConstructed = false

hhGoodPVCancellationBeforeScalarizationClosedIsTrue :
  hhGoodPVCancellationBeforeScalarizationClosed ≡ true
hhGoodPVCancellationBeforeScalarizationClosedIsTrue = refl
