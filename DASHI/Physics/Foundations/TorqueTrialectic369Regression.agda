module DASHI.Physics.Foundations.TorqueTrialectic369Regression where

open import DASHI.Core.Prelude

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque
import DASHI.Reasoning.TernarySynthesisCellComplexExact as Cells
import DASHI.Moonshine.C3FourierConjugationExact as C3

------------------------------------------------------------------------
-- Regression surface for the physical torque specialization.
------------------------------------------------------------------------

positiveXYZ : Torque.BracketVoxel
positiveXYZ =
  SO3.axis₁ , (SO3.axis₂ , SO3.axis₃)

negativeXZY : Torque.BracketVoxel
negativeXZY =
  SO3.axis₁ , (SO3.axis₃ , SO3.axis₂)

degenerateXXY : Torque.BracketVoxel
degenerateXXY =
  SO3.axis₁ , (SO3.axis₁ , SO3.axis₂)

positiveOrientationIsPositive :
  Torque.torqueOrientation positiveXYZ ≡ BT.pos
positiveOrientationIsPositive = refl

reversedOrientationIsNegative :
  Torque.torqueOrientation negativeXZY ≡ BT.neg
reversedOrientationIsNegative = refl

degenerateOrientationIsZero :
  Torque.torqueOrientation degenerateXXY ≡ BT.zero
degenerateOrientationIsZero = refl

swapNegatesOrientation :
  (voxel : Torque.BracketVoxel) →
  Torque.torqueOrientation (Torque.swapTorqueInputs voxel)
  ≡ BT.negate (Torque.torqueOrientation voxel)
swapNegatesOrientation = Torque.swapTorqueInputsNegatesOrientation

swapConjugatesC3Phase :
  (voxel : Torque.BracketVoxel) →
  Torque.torquePhase (Torque.swapTorqueInputs voxel)
  ≡ C3.inversePhase (Torque.torquePhase voxel)
swapConjugatesC3Phase = Torque.swapTorqueInputsConjugatesPhase

pantsFaceRetainsOriginalComparison :
  (voxel : Torque.BracketVoxel) →
  Cells.originalComparisonEdge (Torque.torqueSynthesisTwoCell voxel)
  ≡ Cells.comparisonOneCell (Torque.torqueComparison voxel)
pantsFaceRetainsOriginalComparison = Torque.torqueFaceRetainsComparison

sameTorqueOwnerHasNineEighteenTwentySeven :
  SO3.operatorSheetCount ≡ 9
  × SO3.liftedOperatorSheetCount ≡ 18
  × SO3.bracketVoxelCount ≡ 27
sameTorqueOwnerHasNineEighteenTwentySeven =
  SO3.operatorSheetCountIs9
  , SO3.liftedOperatorSheetCountIs18
  , SO3.bracketVoxelCountIs27
