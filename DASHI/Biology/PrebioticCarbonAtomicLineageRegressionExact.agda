module DASHI.Biology.PrebioticCarbonAtomicLineageRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Biology.AtomicMolecularBiologicalIncorporationHyperfabricExact as Bio
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon
import DASHI.Biology.PrebioticChemistryLifeInevitabilityBidiExact as Prebiotic
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem

------------------------------------------------------------------------
-- Carbon / prebiotic / Levin lineage regression.
--
-- Carbon's atomic/valence identity can be carried into molecular/reaction
-- networks and maintained nonequilibrium systems.  That material continuity is
-- scientifically useful but does not promote abiogenesis, open-ended evolution
-- or agency from chemistry alone.
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

carbonSuitabilityBoundary : Carbon.CarbonChemicalSuitabilityBoundary
carbonSuitabilityBoundary = Carbon.canonicalCarbonChemicalSuitabilityBoundary

prebioticBoundary : Prebiotic.PrebioticChemistryLifeInevitabilityBoundary
prebioticBoundary = Prebiotic.canonicalPrebioticChemistryLifeInevitabilityBoundary

problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary

record PrebioticCarbonAtomicLineageRegression : Set where
  constructor prebioticCarbonAtomicLineageRegression
  field
    carbonLineage : Lineage.AtomicLineage
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
    "The same carbon atomic lineage can be tracked through progressively organised chemistry, but carbon suitability, autocatalysis, compartments and maintained nonequilibrium remain upstream constraints rather than definitions of life or agency. Levin-style problem-space navigation requires explicit observables, moves, targets and correction receipts at the biological organisation level."
