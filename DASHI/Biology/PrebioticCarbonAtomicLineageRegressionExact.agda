module DASHI.Biology.PrebioticCarbonAtomicLineageRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Chemistry.AtomicLineageBidiDiscriminatorExact as Bidi
import DASHI.Biology.AtomicMolecularBiologicalIncorporationHyperfabricExact as Bio
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon
import DASHI.Biology.PrebioticChemistryLifeInevitabilityBidiExact as Prebiotic
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem

------------------------------------------------------------------------
-- Carbon / prebiotic / Levin lineage regression.
------------------------------------------------------------------------

carbonAtomicLineage : Lineage.AtomicLineage
carbonAtomicLineage =
  Lineage.atomicLineage
    "C-12 representative lineage"
    (Atomic369.atomicIndex 6 6 6)
    "369 atomic/valence carrier; neutral representative C-12 atom"
    "carbon-bearing molecular/reaction network"
    "representative C-12 coordinate; isotope choice does not define all carbon chemistry"
    "369 atomic generator -> carbon suitability -> prebiotic reaction-network lane"

siliconAtomicLineage : Lineage.AtomicLineage
siliconAtomicLineage =
  Lineage.atomicLineage
    "Si-28 representative lineage"
    (Atomic369.atomicIndex 14 14 14)
    "369 atomic/valence carrier; neutral representative Si-28 atom"
    "alternative-backbone molecular/reaction network candidate"
    "representative Si-28 coordinate; isotope choice does not define all silicon chemistry"
    "369 atomic generator -> competing-backbone residual in carbon-suitability lane"

carbonSuitabilityBoundary : Carbon.CarbonChemicalSuitabilityBoundary
carbonSuitabilityBoundary = Carbon.canonicalCarbonChemicalSuitabilityBoundary

prebioticBoundary : Prebiotic.PrebioticChemistryLifeInevitabilityBoundary
prebioticBoundary = Prebiotic.canonicalPrebioticChemistryLifeInevitabilityBoundary

problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary

canonicalCarbonSiliconBidiCandidate : Bidi.LineageDiscriminatorCandidate
canonicalCarbonSiliconBidiCandidate =
  Bidi.lineageDiscriminatorCandidate
    "carbon-vs-silicon backbone reachable-chemistry discriminator"
    Bidi.alternativeBackbonePerturbation
    "H0: candidate backbones are equivalent for the declared prebiotic consumer; H1: carbon's stability/reactivity/catenation/aqueous-redox trade space yields a materially larger viable reaction/organisation cone"
    "shared coarse tetravalence or selected valence-class coordinates do not identify complete chemistry"
    "compare matched carbon- and silicon-centred molecular/reaction families under declared solvent/temperature/pressure/redox environments"
    "experimental/computational protocol authority required; no claim about all possible life substrates"
    "isotope/element-resolved backbone lineage and product atom maps"
    "redox/electron-equivalent and electronic-structure readouts"
    "bond diversity, bond energies, geometry, hydrolysis/condensation and network-stability readouts"
    "products/byproducts and reachable reaction-network inventory"
    "autocatalysis/compartment/nonequilibrium persistence readouts only where independently implemented"
    "consumer: discriminate chemical suitability for a declared prebiotic network, not prove life inevitability"
    "solvent, temperature, pressure, abundance, oxidation state, catalysts, water activity and kinetic accessibility"
    "matched analytical/computational chemistry calibration"
    "separation if one backbone supports a larger stable-yet-reactive reachable network under matched environmental constraints"
    "CarbonChemicalSuitabilityLifeBoundaryExact + acquired comparative chemistry evidence"

record PrebioticCarbonAtomicLineageRegression : Set where
  constructor prebioticCarbonAtomicLineageRegression
  field
    carbonLineage : Lineage.AtomicLineage
    alternativeSiliconLineage : Lineage.AtomicLineage
    bidiCandidate : Bidi.LineageDiscriminatorCandidate
    molecularAvailabilityReference : String
    reactionNetworkReference : String
    autocatalysisReference : String
    compartmentReference : String
    nonequilibriumMaintenanceReference : String
    openEndedEvolutionReference : String
    materialLineageAcrossOrganisationStagesRetained : Bool
    materialLineageAcrossOrganisationStagesRetainedIsTrue :
      materialLineageAcrossOrganisationStagesRetained ≡ true
    carbonLineageProvesAbiogenesis : Bool
    carbonLineageProvesAbiogenesisIsFalse :
      carbonLineageProvesAbiogenesis ≡ false
    carbonSuitabilityProvesUniqueLifeSubstrate : Bool
    carbonSuitabilityProvesUniqueLifeSubstrateIsFalse :
      carbonSuitabilityProvesUniqueLifeSubstrate ≡ false
    autocatalysisProvesLife : Bool
    autocatalysisProvesLifeIsFalse : autocatalysisProvesLife ≡ false
    maintainedNonequilibriumProvesAgency : Bool
    maintainedNonequilibriumProvesAgencyIsFalse :
      maintainedNonequilibriumProvesAgency ≡ false
    problemSpaceAgencyRequiresOwnObserverMoveTargetReceipts : Bool
    problemSpaceAgencyRequiresOwnObserverMoveTargetReceiptsIsTrue :
      problemSpaceAgencyRequiresOwnObserverMoveTargetReceipts ≡ true
    alternativeBackboneAndEnvironmentResidualRetained : Bool
    alternativeBackboneAndEnvironmentResidualRetainedIsTrue :
      alternativeBackboneAndEnvironmentResidualRetained ≡ true
    regressionReading : String

open PrebioticCarbonAtomicLineageRegression public

canonicalPrebioticCarbonAtomicLineageRegression :
  PrebioticCarbonAtomicLineageRegression
canonicalPrebioticCarbonAtomicLineageRegression =
  prebioticCarbonAtomicLineageRegression
    carbonAtomicLineage
    siliconAtomicLineage
    canonicalCarbonSiliconBidiCandidate
    "Prebiotic.molecularAvailability"
    "Prebiotic.reactionNetwork"
    "Prebiotic.autocatalyticOrganisation"
    "Prebiotic.compartmentalisedNetwork"
    "Prebiotic.maintainedNonequilibriumSystem"
    "Prebiotic.openEndedEvolutionCandidate"
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    "The same carbon atomic lineage can be tracked through progressively organised chemistry, while the silicon/alternative-backbone residual remains live. Carbon suitability, autocatalysis, compartments and maintained nonequilibrium remain upstream constraints rather than definitions of life or agency. Levin-style problem-space navigation requires explicit observables, moves, targets and correction receipts at the biological organisation level."
