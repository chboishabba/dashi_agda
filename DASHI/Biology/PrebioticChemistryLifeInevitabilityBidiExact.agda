module DASHI.Biology.PrebioticChemistryLifeInevitabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Governance.LevinAgenticMaterialRealisedTopologyCrossPollinationExact as Levin
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon
import DASHI.Physics.Foundations.FundamentalConstantViabilityFibreExact as Viability

------------------------------------------------------------------------
-- PREBIOTIC CHEMISTRY / LIFE-INEVITABILITY BIDI FRONTIER
--
-- Carbon suitability and cosmic parameter viability are now explicit upstream
-- coordinates.  Neither is allowed to collapse the chemistry-to-life frontier:
-- a universe can admit stars/complex chemistry without abiogenesis, and carbon
-- can be chemically privileged without proving life, uniqueness, or inevitability.
------------------------------------------------------------------------

data ChemicalOrganisationStage : Set where
  molecularAvailability
  reactionNetwork
  autocatalyticOrganisation
  compartmentalisedNetwork
  maintainedNonequilibriumSystem
  openEndedEvolutionCandidate
  : ChemicalOrganisationStage

record PrebioticTransitionReceipt : Set where
  constructor prebiotic-transition-receipt
  field
    geochemicalContextReference : String
    cosmicViabilityReference : String
    molecularInventoryReference : String
    carbonBackboneSuitabilityReference : String
    reactionNetworkReference : String
    energyGradientReference : String
    autocatalysisReference : String
    compartmentReference : String
    replicationReference : String
    metabolismReference : String
    boundaryMaintenanceReference : String
    heredityVariationSelectionReference : String
    perturbationRecoveryReference : String
    historicalPathReference : String
    alternativeChemistryReference : String
    observationProvenanceReference : String
    validationReference : String

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

problemBoundary : Problem.ProblemSpaceAgencyBoundary
problemBoundary = Problem.canonicalProblemSpaceAgencyBoundary

autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary

levinBoundary : Levin.LevinAgenticMaterialRealisedTopologyBoundary
levinBoundary = Levin.canonicalLevinAgenticMaterialRealisedTopologyBoundary

carbonBoundary : Carbon.CarbonChemicalSuitabilityBoundary
carbonBoundary = Carbon.canonicalCarbonChemicalSuitabilityBoundary

viabilityBoundary : Viability.FundamentalConstantViabilityBoundary
viabilityBoundary = Viability.canonicalFundamentalConstantViabilityBoundary

record PrebioticChemistryLifeInevitabilityBoundary : Set where
  constructor prebiotic-chemistry-life-inevitability-boundary
  field
    biomoleculeFormationImpliesLife : Bool
    biomoleculeFormationImpliesLifeIsFalse : biomoleculeFormationImpliesLife ≡ false
    autocatalysisImpliesLife : Bool
    autocatalysisImpliesLifeIsFalse : autocatalysisImpliesLife ≡ false
    selfAssemblyImpliesLife : Bool
    selfAssemblyImpliesLifeIsFalse : selfAssemblyImpliesLife ≡ false
    carbonSuitabilityImpliesAbiogenesis : Bool
    carbonSuitabilityImpliesAbiogenesisIsFalse : carbonSuitabilityImpliesAbiogenesis ≡ false
    cosmicViabilityImpliesAbiogenesis : Bool
    cosmicViabilityImpliesAbiogenesisIsFalse : cosmicViabilityImpliesAbiogenesis ≡ false
    chemicalComplexityImpliesAgency : Bool
    chemicalComplexityImpliesAgencyIsFalse : chemicalComplexityImpliesAgency ≡ false
    agenticMaterialEvidenceImpliesOpenEndedEvolution : Bool
    agenticMaterialEvidenceImpliesOpenEndedEvolutionIsFalse :
      agenticMaterialEvidenceImpliesOpenEndedEvolution ≡ false
    oneSuccessfulAbiogenesisRouteProvesLifeInevitable : Bool
    oneSuccessfulAbiogenesisRouteProvesLifeInevitableIsFalse :
      oneSuccessfulAbiogenesisRouteProvesLifeInevitable ≡ false
    repeatedIndependentEmergenceCouldDiscriminateInevitabilityHypotheses : Bool
    repeatedIndependentEmergenceCouldDiscriminateInevitabilityHypothesesIsTrue :
      repeatedIndependentEmergenceCouldDiscriminateInevitabilityHypotheses ≡ true
    chemistryToLifeClaimNeedsPathAndEnvironmentReceipts : Bool
    chemistryToLifeClaimNeedsPathAndEnvironmentReceiptsIsTrue :
      chemistryToLifeClaimNeedsPathAndEnvironmentReceipts ≡ true
    lifeLikeOrganisationCanBeStudiedWithoutSettlingPhenomenology : Bool
    lifeLikeOrganisationCanBeStudiedWithoutSettlingPhenomenologyIsTrue :
      lifeLikeOrganisationCanBeStudiedWithoutSettlingPhenomenology ≡ true
    reading : String

canonicalPrebioticChemistryLifeInevitabilityBoundary :
  PrebioticChemistryLifeInevitabilityBoundary
canonicalPrebioticChemistryLifeInevitabilityBoundary =
  prebiotic-chemistry-life-inevitability-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    "Prebiotic chemistry is an active BIDI frontier downstream of cosmic viability and chemical substrate suitability. Viable constants, stars, carbon production, carbon-rich chemistry, self-assembly and autocatalysis are progressively useful constraints but none alone closes abiogenesis, agency, open-ended evolution, consciousness or life inevitability."
