module DASHI.Biology.CarbonSiliconReachableChemistryBenchmarkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.PrebioticCarbonAtomicLineageRegressionExact as CarbonLineage
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon
import DASHI.Chemistry.CarbonBackboneReachableChemistryConeExact as Cone
import DASHI.Chemistry.AtomicLineageBidiDiscriminatorExact as Bidi

------------------------------------------------------------------------
-- Matched-environment carbon/silicon benchmark.  The result is an experimental
-- design surface, not a pre-decided theorem that carbon must win every context.
------------------------------------------------------------------------

data ReachableChemistryCoordinate : Set where
  stableBondDiversity : ReachableChemistryCoordinate
  stabilityReactivityBalance : ReachableChemistryCoordinate
  geometryAndStereoDiversity : ReachableChemistryCoordinate
  hydrolysisResistance : ReachableChemistryCoordinate
  condensationAccessibility : ReachableChemistryCoordinate
  redoxDiversity : ReachableChemistryCoordinate
  solventCompatibility : ReachableChemistryCoordinate
  polymerReachability : ReachableChemistryCoordinate
  catalyticNetworkReachability : ReachableChemistryCoordinate
  autocatalyticClosureCandidate : ReachableChemistryCoordinate

record BackboneEnvironment : Set where
  constructor backboneEnvironment
  field
    solventReference : String
    temperatureReference : String
    pressureReference : String
    pHReference : String
    redoxReference : String
    elementalAbundanceReference : String
    mineralCatalystReference : String
    energyGradientReference : String

open BackboneEnvironment public

matchedPrebioticEnvironment : BackboneEnvironment
matchedPrebioticEnvironment = backboneEnvironment
  "matched solvent family; water is one explicit reference case"
  "matched temperature grid"
  "matched pressure grid"
  "matched pH grid"
  "matched redox/electron-donor-acceptor envelope"
  "normalize/record C versus Si and heteroatom availability rather than assume equal cosmic abundance"
  "matched mineral/catalyst panel"
  "matched thermal/photochemical/electrochemical energy-gradient panel"

record BackboneReachabilityReceipt : Set where
  constructor backboneReachabilityReceipt
  field
    backboneReference : String
    atomicLineageReference : String
    environment : BackboneEnvironment
    coordinates : List ReachableChemistryCoordinate
    molecularInventoryReference : String
    reactionNetworkReference : String
    productByproductReference : String
    kineticPersistenceReference : String
    competingPathwayReference : String
    observationReference : String
    provenanceReference : String
    numericCalibrationReference : String

open BackboneReachabilityReceipt public

carbonReceipt : BackboneReachabilityReceipt
carbonReceipt = backboneReachabilityReceipt
  "carbon backbone"
  "CarbonLineage.carbonAtomicLineage Z=6"
  matchedPrebioticEnvironment
  ( stableBondDiversity ∷ stabilityReactivityBalance ∷ geometryAndStereoDiversity
  ∷ hydrolysisResistance ∷ condensationAccessibility ∷ redoxDiversity
  ∷ solventCompatibility ∷ polymerReachability ∷ catalyticNetworkReachability
  ∷ autocatalyticClosureCandidate ∷ [] )
  "enumerate/source-pay reachable carbon-bearing molecular inventory"
  "construct source/calculation-backed reaction cone under matched environment"
  "retain yields, side products and dead-end sinks"
  "measure/calculate lifetime and reaction-time distributions"
  "retain alternative routes rather than score only successful carbon pathways"
  "declared chemical-diversity/network consumer"
  "Carbon suitability/cone sources plus benchmark acquisitions"
  "partially unpaid"

siliconReceipt : BackboneReachabilityReceipt
siliconReceipt = backboneReachabilityReceipt
  "silicon backbone"
  "CarbonLineage.siliconAtomicLineage Z=14"
  matchedPrebioticEnvironment
  ( stableBondDiversity ∷ stabilityReactivityBalance ∷ geometryAndStereoDiversity
  ∷ hydrolysisResistance ∷ condensationAccessibility ∷ redoxDiversity
  ∷ solventCompatibility ∷ polymerReachability ∷ catalyticNetworkReachability
  ∷ autocatalyticClosureCandidate ∷ [] )
  "enumerate/source-pay reachable silicon-bearing molecular inventory"
  "construct source/calculation-backed reaction cone under the same environment grid"
  "retain yields, silicate/oxide sinks and competing products"
  "measure/calculate lifetime and reaction-time distributions"
  "retain alternative routes rather than infer inferiority from terrestrial rarity"
  "same declared chemical-diversity/network consumer"
  "silicon chemistry primary/calculation sources to be acquired under same rubric"
  "mostly unpaid"

record CarbonSiliconReachableChemistryBenchmark : Set where
  constructor carbonSiliconReachableChemistryBenchmark
  field
    carbon : BackboneReachabilityReceipt
    silicon : BackboneReachabilityReceipt
    matchedEnvironmentRequired : Bool
    matchedEnvironmentRequiredIsTrue : matchedEnvironmentRequired ≡ true
    sameConsumerRequired : Bool
    sameConsumerRequiredIsTrue : sameConsumerRequired ≡ true
    reachableConeComparisonExplicit : Bool
    reachableConeComparisonExplicitIsTrue : reachableConeComparisonExplicit ≡ true
    carbonPredeclaredWinner : Bool
    carbonPredeclaredWinnerIsFalse : carbonPredeclaredWinner ≡ false
    carbonWinsImpliesLifeInevitable : Bool
    carbonWinsImpliesLifeInevitableIsFalse : carbonWinsImpliesLifeInevitable ≡ false
    carbonWinsProvesUniquePossibleLifeSubstrate : Bool
    carbonWinsProvesUniquePossibleLifeSubstrateIsFalse :
      carbonWinsProvesUniquePossibleLifeSubstrate ≡ false
    benchmarkCreatesAgency : Bool
    benchmarkCreatesAgencyIsFalse : benchmarkCreatesAgency ≡ false
    nextDiscriminatorReference : String

open CarbonSiliconReachableChemistryBenchmark public

canonicalCarbonSiliconReachableChemistryBenchmark : CarbonSiliconReachableChemistryBenchmark
canonicalCarbonSiliconReachableChemistryBenchmark =
  carbonSiliconReachableChemistryBenchmark
    carbonReceipt siliconReceipt
    true refl true refl true refl false refl false refl false refl false refl
    "CarbonLineage.canonicalCarbonSiliconBidiCandidate: matched-environment alternative-backbone perturbation and reaction-cone comparison"
