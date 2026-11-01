module DASHI.Economics.UnitEconomicsMarginExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- GENERIC UNIT-ECONOMICS / MARGIN PRESSURE CALCULUS
------------------------------------------------------------------------

record UnitEconomicsSystem : Set₁ where
  field
    Service User Time : Set
    Price MarginalComputeCost FullyLoadedCost GrossMargin Usage :
      Service → User → Time → Set

open UnitEconomicsSystem public

record HeavyUserSubsidy
    (sys : UnitEconomicsSystem)
    (service : Service sys)
    (user : User sys)
    (time : Time sys) : Set₁ where
  field
    priceObserved      : Price sys service user time
    fullyLoadedObserved : FullyLoadedCost sys service user time
    priceBelowFullyLoadedCost : Set

record UsageGrowthWithMarginCompression
    (sys : UnitEconomicsSystem)
    (service : Service sys)
    (user : User sys)
    (before after : Time sys) : Set₁ where
  field
    usageBefore  : Usage sys service user before
    usageAfter   : Usage sys service user after
    usageIncreased : Set
    marginBefore : GrossMargin sys service user before
    marginAfter  : GrossMargin sys service user after
    marginCompressed : Set

-- One disclosed observation can be interpreted positively by management while
-- also carrying a separately proved risk implication.  Neither interpretation
-- manufactures the other.
record BullishDisclosureRiskDual : Set₁ where
  field
    Observation DeclaredInterpretation RiskInterpretation : Set
    observed : Observation
    declared : DeclaredInterpretation
    risk     : RiskInterpretation

open BullishDisclosureRiskDual public

data HighUsageImpliesPositiveUnitEconomicsPermission : Set where

data BullishInterpretationImpliesLowRiskPermission : Set where

highUsageDoesNotAutoPromoteToPositiveUnitEconomics :
  HighUsageImpliesPositiveUnitEconomicsPermission → ⊥
highUsageDoesNotAutoPromoteToPositiveUnitEconomics ()

bullishInterpretationDoesNotAutoPromoteToLowRisk :
  BullishInterpretationImpliesLowRiskPermission → ⊥
bullishInterpretationDoesNotAutoPromoteToLowRisk ()
