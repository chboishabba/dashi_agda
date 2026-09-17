module DASHI.Biology.Agriculture.AcaciaRhizobialCompetitiveOccupancyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasExact as SenegalAtlas
import DASHI.Biology.Agriculture.AcaciaSenegalSymbiosisEnvironmentalEnablementExact as Enablement
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- ACACIA RHIZOBIAL COMPETITIVE OCCUPANCY
--
-- Population availability, introduced inoculum identity and realised nodule
-- occupancy are separate empirical objects.  The strongest nursery->field
-- rank reversal in Sarr & Lesueur 2007 is A. nilotica, so this owner is
-- deliberately multi-Acacia and does not manufacture an A. senegal reversal.
------------------------------------------------------------------------

sarrEtAl2005DOI : String
sarrEtAl2005DOI = "10.1007/s00248-004-0077-8"

sarrEtAl2005PMID : String
sarrEtAl2005PMID = "16184338"

sarrLesueur2007DOI : String
sarrLesueur2007DOI = "10.1007/s11274-006-9288-0"

sarrEtAl2005 : Attribution.AttributedSource
sarrEtAl2005 = Attribution.mkDOISource
  "Amadou Sarr; Daniel Neyra; Mohamed Houeibib Ould Mohamed; Noureddine Houeibib; Bozena Lesueur"
  "Rhizobial populations in soils from natural Acacia senegal and Acacia nilotica forests in Mauritania and the Senegal River Valley"
  "Microbial Ecology 50(2):152-162"
  "2005"
  sarrEtAl2005DOI
  "https://doi.org/10.1007/s00248-004-0077-8"
  Attribution.academicArticleSource
  "Natural-population source characterising 82 Acacia-nodulating rhizobial isolates across Mauritania and Senegal River Valley soils. Native rhizobial abundance/diversity varies by soil/site, while molecular groups do not collapse cleanly to host species or geographic origin. Retained as background-population evidence rather than an inoculation-performance theorem."
  Attribution.publicAttribution

sarrLesueur2007 : Attribution.AttributedSource
sarrLesueur2007 = Attribution.mkDOISource
  "Amadou Sarr; Didier Lesueur"
  "Influence of soil fertility on the rhizobial competitiveness for nodulation of Acacia senegal and Acacia nilotica provenances in nursery and field conditions"
  "World Journal of Microbiology and Biotechnology 23(5):705-711"
  "2007"
  sarrLesueur2007DOI
  "https://doi.org/10.1007/s11274-006-9288-0"
  Attribution.academicArticleSource
  "Mixed-inoculum nursery/field source showing that realised nodule occupancy depends on strain, host provenance/species and soil environment. The strongest nursery-to-field ranking reversal reported in the source is for Acacia nilotica; Acacia senegal retains CIRADF300 as the majority occupant. DASHI therefore imports the competitive-occupancy/context distinction but does not assert an Acacia-senegal-specific rank reversal."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Population / inoculum / occupancy roles.
------------------------------------------------------------------------

data OccupancyEvidenceRole : Set where
  indigenousPopulationBackground : OccupancyEvidenceRole
  introducedInoculumMixture : OccupancyEvidenceRole
  nurseryNoduleOccupancy : OccupancyEvidenceRole
  fieldNoduleOccupancy : OccupancyEvidenceRole
  hostSoilCompetitivenessInteraction : OccupancyEvidenceRole

record OccupancyReceipt : Set where
  constructor occupancy-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : OccupancyEvidenceRole
    hostReading : String
    soilReading : String
    strainReading : String
    boundedReading : String
open OccupancyReceipt public

naturalPopulationReceipt : OccupancyReceipt
naturalPopulationReceipt = occupancy-receipt
  sarrEtAl2005
  sarrEtAl2005DOI
  indigenousPopulationBackground
  "natural Acacia senegal and Acacia nilotica forest soils"
  "Mauritania and Senegal River Valley soil/site backgrounds"
  "82 isolates grouped by molecular characterization; background abundance/diversity retained"
  "indigenous population structure is a starting ecological state, not realised occupancy of a later introduced inoculum"

nurseryFieldCompetitionReceipt : OccupancyReceipt
nurseryFieldCompetitionReceipt = occupancy-receipt
  sarrLesueur2007
  sarrLesueur2007DOI
  hostSoilCompetitivenessInteraction
  "Acacia senegal and Acacia nilotica provenances retained separately"
  "low-fertility nursery soil versus more fertile field context"
  "mixed introduced strains with occupancy determined from nodules"
  "occupancy rankings depend on host/soil/phase; A. nilotica supplies the clear rank-reversal example, while A. senegal does not"

------------------------------------------------------------------------
-- Finite DASHI information-loss witness.
------------------------------------------------------------------------

data OccupancyWorld : Set where
  sameStrainNurseryLowFertility : OccupancyWorld
  sameStrainFieldHigherFertility : OccupancyWorld

data OccupancyTask : Set where
  realisedOccupancyTask : OccupancyTask

data StrainToken : Set where
  selectedIntroducedStrain : StrainToken

strainIdentityOnly : OccupancyWorld → StrainToken
strainIdentityOnly _ = selectedIntroducedStrain

realisedOccupancy : OccupancyTask → OccupancyWorld → Bool
realisedOccupancy realisedOccupancyTask sameStrainNurseryLowFertility = false
realisedOccupancy realisedOccupancyTask sameStrainFieldHigherFertility = true

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

strainIdentityNotTaskSufficientForOccupancy :
  LES.TaskFactorisation strainIdentityOnly realisedOccupancy → ⊥
strainIdentityNotTaskSufficientForOccupancy factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor realisedOccupancyTask
      {sameStrainFieldHigherFertility} {sameStrainNurseryLowFertility} refl)

------------------------------------------------------------------------
-- Existing owners reused without source fusion.
------------------------------------------------------------------------

senegalSourceAtlasReused : Attribution.AttributedSourceAtlas
senegalSourceAtlasReused = SenegalAtlas.acaciaAttributedAtlas

environmentalEnablementBoundaryReused : Enablement.EnvironmentalEnablementBoundary
environmentalEnablementBoundaryReused = Enablement.canonicalEnvironmentalEnablementBoundary

genericBacterialFluxStillOpen :
  Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
genericBacterialFluxStillOpen = refl

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record CompetitiveOccupancyBoundary : Set where
  constructor competitive-occupancy-boundary
  field
    strainIdentityAloneDeterminesNoduleOccupancy : Bool
    indigenousPopulationAndSoilContextMustRemainIndexed : Bool
    introducedMixtureAndNaturalPopulationAreSameObject : Bool
    nurseryOccupancyImpliesFieldOccupancy : Bool
    hostSpeciesAndProvenanceMustRemainIndexed : Bool
    soilFertilityAndPhaseMustRemainIndexed : Bool
    multiAcaciaTransitionCreatesAcaciaSenegalRankReversal : Bool
    noduleOccupancyImpliesFixedNFlux : Bool
    occupancyImpliesWholePlantAssimilation : Bool
    occupancyCreatesDeploymentAuthority : Bool
    syntheticOccupancyWorldsAreSourceMeasurements : Bool
open CompetitiveOccupancyBoundary public

canonicalOccupancyBoundary : CompetitiveOccupancyBoundary
canonicalOccupancyBoundary = competitive-occupancy-boundary
  false true false false true true false false false false false

attributionRule : String
attributionRule =
  "Sarr et al. 2005 (DOI 10.1007/s00248-004-0077-8; PMID 16184338) owns its natural Acacia-senegal/Acacia-nilotica soil-rhizobial population propositions. Sarr & Lesueur 2007 (DOI 10.1007/s11274-006-9288-0) owns its mixed-inoculum nursery/field competitive-occupancy propositions. The strong nursery-to-field rank reversal in that paper is retained as Acacia-nilotica evidence and is not relabelled as an Acacia-senegal reversal. DASHI owns only the population/inoculum/occupancy separation, synthetic TaskFactorisation witness and no-promotion boundary. Nodule occupancy is not promoted to fixed-N flux, plant assimilation or deployment authority."
