module DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastRecallArithmeticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- SOURCE-EXACT FINITE ARITHMETIC FOR DOI 10.1029/2023SW003522
--
-- The paper reports 229 CME-driven events: 166 storm events with Kp >= 5 and
-- 63 non-storm events with Kp < 5.  Of the 166 storm events, 129 were reported
-- accurately predicted, quoted as 77.7% recall.  The decimal percentage is a
-- rounded presentation; here we keep the exact count ratio and bracket it by
-- integer cross-products between 777/1000 and 778/1000.
------------------------------------------------------------------------

totalEvents : Nat
totalEvents = 229

stormEvents : Nat
stormEvents = 166

nonStormEvents : Nat
nonStormEvents = 63

accuratelyPredictedStormEvents : Nat
accuratelyPredictedStormEvents = 129

reportedRecallPerMille : Nat
reportedRecallPerMille = 777

eventPartitionCloses : stormEvents + nonStormEvents ≡ totalEvents
eventPartitionCloses = refl

-- 777 * 166 = 128982, while 129 * 1000 = 129000.
-- The positive residual 18 certifies that 129/166 is above 0.777.
lowerRecallBracketResidual : Nat
lowerRecallBracketResidual = 18

lowerRecallBracketCloses :
  reportedRecallPerMille * stormEvents + lowerRecallBracketResidual
  ≡ accuratelyPredictedStormEvents * 1000
lowerRecallBracketCloses = refl

-- 778 * 166 = 129148, which exceeds 129000 by 148.
-- This certifies that 129/166 is below 0.778.
upperRecallBracketResidual : Nat
upperRecallBracketResidual = 148

upperRecallBracketCloses :
  accuratelyPredictedStormEvents * 1000 + upperRecallBracketResidual
  ≡ 778 * stormEvents
upperRecallBracketCloses = refl

record RecallCountWitness : Set where
  constructor recall-count-witness
  field
    total : Nat
    storms : Nat
    nonStorms : Nat
    correctStormPredictions : Nat
    displayedPerMille : Nat
    lowerCrossProductResidual : Nat
    upperCrossProductResidual : Nat

sourceRecallWitness : RecallCountWitness
sourceRecallWitness = recall-count-witness
  totalEvents stormEvents nonStormEvents accuratelyPredictedStormEvents
  reportedRecallPerMille lowerRecallBracketResidual upperRecallBracketResidual

roundedRecallDoesNotPayOperationalThreshold : Bool
roundedRecallDoesNotPayOperationalThreshold = false

recallCountDoesNotPayForecastCausality : Bool
recallCountDoesNotPayForecastCausality = false

recallCountDoesNotPayIndependentReplication : Bool
recallCountDoesNotPayIndependentReplication = false
