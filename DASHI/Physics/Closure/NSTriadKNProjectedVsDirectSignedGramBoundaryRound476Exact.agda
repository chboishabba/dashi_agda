module DASHI.Physics.Closure.NSTriadKNProjectedVsDirectSignedGramBoundaryRound476Exact where

------------------------------------------------------------------------
-- ROUND476 / DO NOT IDENTIFY PROJECTED OUTER GRAM WITH R440 DIRECT CROSS
--
-- Lean's `outerCellVec` GramOperatorBound is a fixed-output theorem on outer
-- cells lying in k-perp.  The mature Agda R440 direct signed-companion route is
-- different: its left amplitude aggregate is intentionally generic, while the
-- R286 mixed amplitude cell is not generically transverse to k.
--
-- Consequently
--
--   projected outer-cell Gram route
--
-- and
--
--   unprojected R440 signed companion cross route
--
-- are distinct sufficient producers.  A Leray insertion theorem may connect
-- them only when an independent output-transversality receipt for the tested
-- amplitude is available.  This owner records that type boundary explicitly so
-- future compilers cannot silently insert P_k.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicitySplitRound286Exact as R286
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact as R471
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact as R475

data FixedOutputGramLane : Set where
  projectedOuterGramOperator : FixedOutputGramLane
  directSignedCompanionCross : FixedOutputGramLane

preferredProjectedConsumer : FixedOutputGramLane
preferredProjectedConsumer = projectedOuterGramOperator

directSignedFallbackConsumer : FixedOutputGramLane
directSignedFallbackConsumer = directSignedCompanionCross

round476ProjectedOuterGramAndR440DirectCrossDefinitionallySame : Bool
round476ProjectedOuterGramAndR440DirectCrossDefinitionallySame = false

round476R440AmplitudeGenericInOutputTransversality : Bool
round476R440AmplitudeGenericInOutputTransversality = true

round476R286MixedCellGenericallyOutputTransverse : Bool
round476R286MixedCellGenericallyOutputTransverse = false

round476LerayInsertionRequiresSeparateAmplitudeTransversality : Bool
round476LerayInsertionRequiresSeparateAmplitudeTransversality = true

round476ProjectedGramConsumerAvailable : Bool
round476ProjectedGramConsumerAvailable =
  R471.round471GramOperatorBoundIsPreferredConsumer

round476ProjectedGramTwoScalarCompilerAvailable : Bool
round476ProjectedGramTwoScalarCompilerAvailable =
  R475.round475TwoScalarBoundsCompileToPhysicalGramOperator

round476R440DirectSignedSameObjectCompilerAvailable : Bool
round476R440DirectSignedSameObjectCompilerAvailable =
  R440.round440R299PhysicalDoubleSumSameObjectIdentificationClosed

round476PackageAClosed : Bool
round476PackageAClosed = false

round476ClayPromotion : Bool
round476ClayPromotion = false

round476ProjectedOuterGramAndR440DirectCrossDefinitionallySameIsFalse :
  round476ProjectedOuterGramAndR440DirectCrossDefinitionallySame ≡ false
round476ProjectedOuterGramAndR440DirectCrossDefinitionallySameIsFalse = refl

round476R286MixedCellGenericallyOutputTransverseIsFalse :
  round476R286MixedCellGenericallyOutputTransverse ≡ false
round476R286MixedCellGenericallyOutputTransverseIsFalse = refl
