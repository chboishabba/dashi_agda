module DASHI.Governance.PlanetaryBoundaryAllocationExact where

open import DASHI.Core.Prelude
open import DASHI.Governance.SafeJustIndicatorSystemExact

------------------------------------------------------------------------
-- PLANETARY BOUNDARY ALLOCATION
--
-- O'Neill et al. (2018) downscale global boundaries to equal per-capita
-- quantities for their universal-sufficiency research question.  The global
-- Earth-system limit and the normative allocation rule are kept as different
-- typed coordinates.
------------------------------------------------------------------------

data AllocationRule : Set where
  equalPerCapita grandfathering historicalResponsibility sufficiencyBased : AllocationRule

record GlobalBoundary : Set where
  constructor globalBoundary
  field
    indicator : BiophysicalIndicator
    globalBudgetCode : Nat

open GlobalBoundary public

record PopulationBasis : Set where
  constructor populationBasis
  field
    populationCode : Nat

record PerCapitaBoundary : Set where
  constructor perCapitaBoundary
  field
    sourceIndicator : BiophysicalIndicator
    sourceGlobalBudgetCode : Nat
    allocationRule : AllocationRule
    populationBasisCode : Nat

-- A provenance-preserving symbolic downscale.  Arithmetic values and units are
-- supplied by the empirical dataset; this owner records which transformation
-- produced a national/per-capita threshold rather than pretending that an
-- ethical allocation rule is itself an Earth-system measurement.
downscale : AllocationRule → GlobalBoundary → PopulationBasis → PerCapitaBoundary
downscale rule g p =
  perCapitaBoundary (indicator g) (globalBudgetCode g) rule (PopulationBasis.populationCode p)

canonicalGlobalCO2 : GlobalBoundary
canonicalGlobalCO2 = globalBoundary co2Emissions 1

canonicalPopulation : PopulationBasis
canonicalPopulation = populationBasis 1

paperCO2Allocation : PerCapitaBoundary
paperCO2Allocation = downscale equalPerCapita canonicalGlobalCO2 canonicalPopulation

paperUsesEqualPerCapita : allocationRule paperCO2Allocation ≡ equalPerCapita
paperUsesEqualPerCapita = refl

record AllocationBoundary : Set where
  constructor allocationBoundary
  field
    globalBoundaryDeterminesUniqueEthicalAllocation : Bool
    globalBoundaryDeterminesUniqueEthicalAllocationIsFalse :
      globalBoundaryDeterminesUniqueEthicalAllocation ≡ false
    equalPerCapitaIsExplicitConvention : Bool
    equalPerCapitaIsExplicitConventionIsTrue : equalPerCapitaIsExplicitConvention ≡ true
    changingAllocationRuleChangesEarthSystemMeasurement : Bool
    changingAllocationRuleChangesEarthSystemMeasurementIsFalse :
      changingAllocationRuleChangesEarthSystemMeasurement ≡ false

canonicalAllocationBoundary : AllocationBoundary
canonicalAllocationBoundary = allocationBoundary false refl true refl false refl
