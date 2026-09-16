module DASHI.Biology.Protein.ProteinConsumerFamilyBiocontrolCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Biology.Protein.ProteinConsumerProjectionAdequacyExact as Portfolio
import DASHI.Biology.Protein.ProteinConsumerFamilyRefinementKernelExact as Protein
import DASHI.Environment.BiocontrolChemistryObserverParetoExact as Biocontrol

------------------------------------------------------------------------
-- PROTEIN <-> BIOCONTROL CONSUMER-FAMILY CROSS-POLLINATION
--
-- This owner records only the shared formal architecture:
--
--   declared consumer
--     -> projection defect / adequacy predicate
--     -> local retained-coordinate repair
--     -> eligible model
--     -> minimal/Pareto selection.
--
-- It does not transfer protein biology into ecology/chemistry, chemistry into
-- protein mechanism, source attribution, empirical costs, or authority.
------------------------------------------------------------------------

proteinThermalSelectionDonor :
  MDL.MinimalEligibleDescription
    (Protein.problemFor Portfolio.thermalResponseConsumer)
    Protein.identityPlusResidue
proteinThermalSelectionDonor =
  Protein.minimalFor Portfolio.thermalResponseConsumer

proteinRateSelectionDonor :
  MDL.MinimalEligibleDescription
    (Protein.problemFor Portfolio.transitionRateConsumer)
    Protein.topologyPlusRate
proteinRateSelectionDonor =
  Protein.minimalFor Portfolio.transitionRateConsumer

biocontrolSpeciesSelectionDonor :
  MDL.MinimalEligibleDescription
    Biocontrol.speciesProblem
    Biocontrol.speciesSensitive
biocontrolSpeciesSelectionDonor = Biocontrol.speciesMinimalEligible

biocontrolContextualSelectionDonor :
  MDL.MinimalEligibleDescription
    Biocontrol.contextualProblem
    Biocontrol.contextualChemistry
biocontrolContextualSelectionDonor = Biocontrol.contextualMinimalEligible

------------------------------------------------------------------------
-- Shared architectural coordinates only.
------------------------------------------------------------------------

record ConsumerFamilyArchitecture : Set where
  constructor consumer-family-architecture
  field
    lane : String
    coarseSurface : String
    retainedRepair : String
    consumer : String
    rankingRule : String
    attributionRule : String
open ConsumerFamilyArchitecture public

proteinArchitecture : ConsumerFamilyArchitecture
proteinArchitecture = consumer-family-architecture
  "protein"
  "identity / sequence / topology / cysteine-presence projections can be too coarse for declared protein consumers"
  "retain only the query-relevant residue, environment, rate, or accessibility coordinate family"
  "thermal response / resolved conformation / transition rate / thiol modification"
  "consumer adequacy and admissibility first; minimal description only afterward"
  "Feng/TRPA1, structural AdK, Li-Liu-Ji/AdK, and Allium sources keep ownership only of their domain premises; selection kernel is DASHI synthesis"

biocontrolArchitecture : ConsumerFamilyArchitecture
biocontrolArchitecture = consumer-family-architecture
  "biocontrol chemistry/ecology"
  "bulk-only or species-only chemistry observation can be too coarse for declared chemistry/ecology consumers"
  "retain analyte/species/fraction context and, when required, site/season/window/protocol/uncertainty coordinates"
  "species/fraction classification / contextual ecological classification"
  "consumer adequacy and admissibility first; minimal description/Pareto ranking only afterward"
  "biocontrol chemistry/ecology sources and repository fixtures remain local to that lane; cross-pollination contributes no protein biology"

sharedAdequacyBeforeRankingArchitecture : Bool
sharedAdequacyBeforeRankingArchitecture = true

sharedCrossDomainPattern : String
sharedCrossDomainPattern =
  "projection defect -> local retained-coordinate repair -> eligibility -> minimal/Pareto selection; the shared object is the formal selection architecture, not a shared biological or chemical mechanism"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ProteinBiologyTransfersToBiocontrol : Set where
data BiocontrolChemistryTransfersToProtein : Set where
data ProteinSourceAttributionTransfersToBiocontrol : Set where
data BiocontrolSourceAttributionTransfersToProtein : Set where
data SharedMDLArchitectureCreatesSharedMechanism : Set where

aProteinBiologyDoesNotTransfer : ProteinBiologyTransfersToBiocontrol → ⊥
aProteinBiologyDoesNotTransfer ()

biocontrolChemistryDoesNotTransfer : BiocontrolChemistryTransfersToProtein → ⊥
biocontrolChemistryDoesNotTransfer ()

proteinAttributionDoesNotTransfer : ProteinSourceAttributionTransfersToBiocontrol → ⊥
proteinAttributionDoesNotTransfer ()

biocontrolAttributionDoesNotTransfer : BiocontrolSourceAttributionTransfersToProtein → ⊥
biocontrolAttributionDoesNotTransfer ()

sharedArchitectureDoesNotCreateSharedMechanism : SharedMDLArchitectureCreatesSharedMechanism → ⊥
sharedArchitectureDoesNotCreateSharedMechanism ()

proteinBiologyTransfersToBiocontrol : Bool
proteinBiologyTransfersToBiocontrol = false

biocontrolChemistryTransfersToProtein : Bool
biocontrolChemistryTransfersToProtein = false

crossDomainSourceAttributionTransfers : Bool
crossDomainSourceAttributionTransfers = false

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProteinBiocontrolCrossPollinationBoundary : Set where
  constructor protein-biocontrol-cross-pollination-boundary
  field
    sharedAdequacyBeforeRanking : Bool
    proteinMinimalSelectionRetained : Bool
    biocontrolMinimalSelectionRetained : Bool
    sharedMechanismClaimed : Bool
    proteinBiologyTransfers : Bool
    biocontrolChemistryTransfers : Bool
    sourceAttributionTransfers : Bool
    identityMetadataTransfersAuthority : Bool
open ProteinBiocontrolCrossPollinationBoundary public

canonicalProteinBiocontrolCrossPollinationBoundary :
  ProteinBiocontrolCrossPollinationBoundary
canonicalProteinBiocontrolCrossPollinationBoundary =
  protein-biocontrol-cross-pollination-boundary
    true true true false false false false false
