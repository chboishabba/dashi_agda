module DASHI.Economics.JPYTreasuryOpposingFlow20261121Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool)
import DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact as Yen
import DASHI.Economics.GlobalFundingLiquidityRealisationExact as Funding
import DASHI.Economics.GeopoliticalEnergyAITreasuryTransmissionExact as Geo

-- Signed opposing yield pressure, not calibrated bond-price elasticities.
-- A unit here is a synthetic common-basis contribution, not a basis point.
record TreasuryOpposingPressure : Set where
  constructor treasuryOpposingPressure
  field
    safeHavenBuying : Nat
    easingExpectation : Nat
    japaneseRepatriation : Nat
    forcedTreasurySelling : Nat
    supplyAndTermPremium : Nat
open TreasuryOpposingPressure public

downward : TreasuryOpposingPressure → Nat
downward s = safeHavenBuying s + easingExpectation s

upward : TreasuryOpposingPressure → Nat
upward s = japaneseRepatriation s + forcedTreasurySelling s + supplyAndTermPremium s

data YieldOutcome : Set where
  lowerYield higherYield balancedYield : YieldOutcome

-- Exact witness of a strictly positive integer gap, avoiding assumptions
-- about the empirical unit and sign of any particular constituent.
data Classified (s : TreasuryOpposingPressure) : Set where
  lowerBy : (gap : Nat) → upward s + suc gap ≡ downward s → Classified s
  higherBy : (gap : Nat) → downward s + suc gap ≡ upward s → Classified s
  tied : downward s ≡ upward s → Classified s

outcome : ∀ {s} → Classified s → YieldOutcome
outcome (lowerBy _ _) = lowerYield
outcome (higherBy _ _) = higherYield
outcome (tied _) = balancedYield

flightFixture : TreasuryOpposingPressure
flightFixture = treasuryOpposingPressure 8 2 3 2 1

repatriationFixture : TreasuryOpposingPressure
repatriationFixture = treasuryOpposingPressure 1 1 3 2 1

sameJPYComponent :
  japaneseRepatriation flightFixture ≡ japaneseRepatriation repatriationFixture
sameJPYComponent = refl

sameForcedSaleComponent :
  forcedTreasurySelling flightFixture ≡ forcedTreasurySelling repatriationFixture
sameForcedSaleComponent = refl

flightLower : Classified flightFixture
flightLower = lowerBy 3 refl

repatriationHigher : Classified repatriationFixture
repatriationHigher = higherBy 3 refl

oppositeOutcomeDespiteSameJPY :
  (outcome flightLower ≡ lowerYield) ×
  (outcome repatriationHigher ≡ higherYield)
oppositeOutcomeDespiteSameJPY = refl , refl

-- Cross-owner attachment records evidence gates, but supplies none.
record TreasuryFlowJoin : Set where
  field
    yenValve : Yen.YenFundingValve
    fundingState : Funding.FundingState
    dollarSystem : Geo.MultiObjectiveDollarSystem
    pressures : TreasuryOpposingPressure
    sameHorizon : Bool
    sourceNormalisationPaid : Bool
    executedFlowPaid : Bool
    actorIntentPaid : Bool

data SameJPYImpliesSameYield : Set where
sameJPYDoesNotDetermineYield : SameJPYImpliesSameYield → ⊥
sameJPYDoesNotDetermineYield ()

data ObservedYieldProvesCrashIntent : Set where
yieldSignDoesNotEstablishIntent : ObservedYieldProvesCrashIntent → ⊥
yieldSignDoesNotEstablishIntent ()
