module DASHI.Biology.PrebioticChemistryLifeInevitabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Governance.LevinAgenticMaterialRealisedTopologyCrossPollinationExact as Levin

------------------------------------------------------------------------
-- PREBIOTIC CHEMISTRY / LIFE-INEVITABILITY BIDI FRONTIER
--
-- Literature calibration only; generic distinctions below are DASHI-owned.
--
-- Otto et al., "From self-replication to replicator systems en route to de
-- novo life", Nature Reviews Chemistry 4 (2020), DOI 10.1038/s41570-020-0196-x.
-- The review treats integration of replication, metabolism,
-- compartmentalisation and out-of-equilibrium maintenance as a major remaining
-- challenge rather than as an already solved chemistry-to-life theorem.
--
-- Singh et al., "Non-equilibrium self-assembly for living matter-like
-- properties", Nature Reviews Chemistry 8 (2024),
-- DOI 10.1038/s41570-024-00640-z.
-- This motivates explicit non-equilibrium and integration coordinates.
--
-- Autocatalytic-set and systems-chemistry literature motivates candidate
-- organisation coordinates but is not promoted here to "life is inevitable".
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
    molecularInventoryReference : String
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

record PrebioticChemistryLifeInevitabilityBoundary : Set where
  constructor prebiotic-chemistry-life-inevitability-boundary
  field
    biomoleculeFormationImpliesLife : Bool
    biomoleculeFormationImpliesLifeIsFalse : biomoleculeFormationImpliesLife ≡ false
    autocatalysisImpliesLife : Bool
    autocatalysisImpliesLifeIsFalse : autocatalysisImpliesLife ≡ false
    selfAssemblyImpliesLife : Bool
    selfAssemblyImpliesLifeIsFalse : selfAssemblyImpliesLife ≡ false
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
    true refl
    true refl
    true refl
    "Prebiotic chemistry is treated as an active BIDI frontier over molecular availability, reaction-network organisation, autocatalysis, compartmentalisation, maintained non-equilibrium dynamics, heredity/variation/selection and historical environment. None of biomolecule formation, self-assembly, autocatalysis or material competency alone proves life, agency, open-ended evolution or inevitability. Repeated independent emergence under controlled variation could instead function as evidence that refines competing inevitability hypotheses."
