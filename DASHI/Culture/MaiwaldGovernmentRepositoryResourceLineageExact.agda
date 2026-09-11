module DASHI.Culture.MaiwaldGovernmentRepositoryResourceLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MAIWALD GOVERNMENT-REPOSITORY / RESOURCE LINEAGE
--
-- Thin source-specific archaeology owner.  It does not replace the project or
-- manifestation owners.  It records the NSF Public Access Repository manuscript
-- as a distinct government-repository manifestation, its exact resource IDs,
-- and the manuscript's own description of the Figure-3 data-production chain.
------------------------------------------------------------------------

record GovernmentRepositoryManuscript : Set where
  constructor government-repository-manuscript
  field
    title : String
    repository : String
    repositoryObjectId : String
    sourceLink : String
    versionOfRecordDoi : String
    preprintDoi : String
    frankMaiwaldAffiliation : String
    explicitNumberedAffiliation : Bool
    fullManuscriptAvailable : Bool
    governmentRepositoryManifestation : Bool
    repositoryManifestationEqualsRawDataset : Bool

open GovernmentRepositoryManuscript public

nsfParProtonatedValine : GovernmentRepositoryManuscript
nsfParProtonatedValine = government-repository-manuscript
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "U.S. National Science Foundation Public Access Repository"
  "NSF PAR purl 10612041"
  "https://par.nsf.gov/servlets/purl/10612041"
  "10.1021/acs.jpca.4c03552"
  "10.26434/chemrxiv-2024-2tvc6"
  "Frank Maiwald, affiliation 2 = NASA Jet Propulsion Laboratory, California Institute of Technology"
  true true true false

------------------------------------------------------------------------
-- Funding/resource identifiers named in the manuscript.
------------------------------------------------------------------------

record MaiwaldResourceLineage : Set where
  constructor maiwald-resource-lineage
  field
    jplNasaPrimeContract : String
    jplProgramme : String
    nsfAward : String
    cuResearchComputingAwards : String
    manuscriptSaysPublishedInRemembrance : Bool
    jplContractPaysPersonSpecificProjectOwnership : Bool
    nsfAwardPaysMaiwaldCustody : Bool
    researchComputingAwardPaysRawSpectraCustody : Bool
    resourceIdentifiersMayRoutePrimarySearch : Bool
    boundedReading : String

open MaiwaldResourceLineage public

protonatedValineResourceLineage : MaiwaldResourceLineage
protonatedValineResourceLineage = maiwald-resource-lineage
  "80NM0018D0004"
  "JPL Strategic University Research Partnership (SURP)"
  "CHE-2154271"
  "ACI-1532235; ACI-1532236"
  true false false false true
  "The manuscript explicitly acknowledges JPL/NASA contract 80NM0018D0004, JPL SURP, NSF CHE-2154271, and CU Boulder Research Computing support. These identifiers pay resource/funding lineage and route acquisition; they do not by themselves establish person-specific ownership, custody, grant transfer, or raw-data location."

------------------------------------------------------------------------
-- Figure-production / raw-data boundary.
------------------------------------------------------------------------

record FigureProductionState : Set where
  constructor figure-production-state
  field
    figure : String
    measuredSpecies : String
    manuscriptRawPointsNamed : Bool
    smoothingNamed : Bool
    smoothingMethod : String
    spectraCollectedAcrossSeveralDays : Bool
    minimumN2ScanCountNamed : Bool
    minimumN2ScanCount : String
    exactScanFilesLocated : Bool
    exactRawDatasetIdentifierLocated : Bool
    figureImageEqualsRawDataset : Bool
    manuscriptPaysRawDataCustody : Bool
    nextAcquisitionTarget : String

open FigureProductionState public

protonatedValineFigure3Production : FigureProductionState
protonatedValineFigure3Production = figure-production-state
  "Figure 3"
  "ValH+·N2 and ValH+·CH4 infrared photodissociation spectra"
  true true
  "full lines are 5-point gliding averages to guide the eye"
  true true
  "at least 50 scans for the reported N2 spectrum"
  false false false false
  "recover scan-level wavelength/intensity assets, reduced-spectrum tables or instrument/data-management manifests that crosswalk the multi-day scans to Figure 3 and the FY23 poster spectra"

------------------------------------------------------------------------
-- Snowball coordinates: external identity and library traversal only.
------------------------------------------------------------------------

record MaiwaldRepositoryCoordinate : Set where
  constructor maiwald-repository-coordinate
  field
    doi : String
    repositoryObject : String
    qid : String
    qidMeaning : String
    deweyTraversal : String
    directLinkRetained : Bool
    qidCreatesPersonIdentity : Bool
    deweyCreatesEvidenceAuthority : Bool

open MaiwaldRepositoryCoordinate public

maiwaldRepositoryCoordinate : MaiwaldRepositoryCoordinate
maiwaldRepositoryCoordinate = maiwald-repository-coordinate
  "10.1021/acs.jpca.4c03552"
  "NSF PAR 10612041"
  "Q189325"
  "Jet Propulsion Laboratory institution coordinate only; Frank Maiwald person QID unresolved"
  "543.5 Spectroscopy / 540 Chemistry; 025.3 metadata traversal only"
  true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record GovernmentRepositoryResourceBoundary : Set where
  constructor government-repository-resource-boundary
  field
    governmentRepositoryCopyCreatesNewScientificIndependence : Bool
    governmentRepositoryCopyEqualsVersionOfRecord : Bool
    fundingIdentifierCreatesCustody : Bool
    primeContractCreatesPersonSpecificOwnership : Bool
    rawPointsVisibleInFigurePayScanFiles : Bool
    smoothingDescriptionPaysReductionProvenanceCompletely : Bool
    graphOrDeweyRouteCreatesAuthority : Bool
    exactIdentifiersImproveAcquisitionRouting : Bool

open GovernmentRepositoryResourceBoundary public

canonicalGovernmentRepositoryResourceBoundary : GovernmentRepositoryResourceBoundary
canonicalGovernmentRepositoryResourceBoundary = government-repository-resource-boundary
  false false false false false false false true
