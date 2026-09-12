module DASHI.Physics.Chemistry.AtomicPeriodicTable369PetrochemicalIdentityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Hyper
import DASHI.Chemistry.ChlorAlkaliCanonicalHalfReactionsExact as Half
import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact as Industrial

------------------------------------------------------------------------
-- PETROCHEMICAL / CHLOR-ALKALI IDENTITY BRIDGE
--
-- Concrete cross-pollination target for the generic chemistry hyperfibre.
-- The main identity lesson is that element/atom identity, molecular-species
-- identity, reaction stoichiometry and industrial process identity are distinct
-- fibres and need separate receipts.
--
-- In particular:
--   chlorine atom != molecular chlorine Cl2
-- and neither object by itself pays the chlor-alkali electrode process.
------------------------------------------------------------------------

record ChemicalIdentityCoordinate : Set where
  constructor chemicalIdentityCoordinate
  field
    label : String
    formula : String
    semanticQid : String
    pubChemCid : String
    chebiId : String
    deweyCoordinate : String
    primaryOrAuthorityLink : String
    sourceRole : String

open ChemicalIdentityCoordinate public

chlorineAtomCoordinate : ChemicalIdentityCoordinate
chlorineAtomCoordinate =
  chemicalIdentityCoordinate
    "atomic chlorine"
    "Cl"
    "Q83006410"
    "5360523"
    "CHEBI:29311"
    "exact species-level Dewey coordinate unresolved"
    "https://pubchem.ncbi.nlm.nih.gov/compound/5360523"
    "authoritative identity coordinate; not a reaction or process receipt"

molecularChlorineCoordinate : ChemicalIdentityCoordinate
molecularChlorineCoordinate =
  chemicalIdentityCoordinate
    "molecular chlorine / dichlorine"
    "Cl2"
    "Q1904422"
    "24526"
    "CHEBI:29310"
    "exact species-level Dewey coordinate unresolved"
    "https://pubchem.ncbi.nlm.nih.gov/compound/24526"
    "authoritative molecular-species identity coordinate"

ethyleneCoordinate : ChemicalIdentityCoordinate
ethyleneCoordinate =
  chemicalIdentityCoordinate
    "ethylene / ethene"
    "C2H4"
    "Q151313"
    "6325"
    "CHEBI:18153"
    "organic-chemistry catalogue neighbourhood; exact item Dewey unresolved"
    "https://pubchem.ncbi.nlm.nih.gov/compound/6325"
    "authoritative molecular identity coordinate; downstream cracker product identity"

vinylChlorideCoordinate : ChemicalIdentityCoordinate
vinylChlorideCoordinate =
  chemicalIdentityCoordinate
    "vinyl chloride / chloroethene"
    "C2H3Cl"
    "Q338869"
    "6338"
    "unresolved in inspected source"
    "organic/polymer chemistry catalogue neighbourhood; exact item Dewey unresolved"
    "https://pubchem.ncbi.nlm.nih.gov/compound/6338"
    "authoritative molecular identity coordinate; VCM identity, not polymerisation validation"

------------------------------------------------------------------------
-- External process-source coordinates.  These are source receipts, not theorem
-- authority for arbitrary crackers or plants.
------------------------------------------------------------------------

record ProcessSourceCoordinate : Set where
  constructor processSourceCoordinate
  field
    processLabel : String
    source : String
    doi : String
    qid : String
    dewey : String
    directLink : String
    role : String

basfSteamCrackerSource : ProcessSourceCoordinate
basfSteamCrackerSource =
  processSourceCoordinate
    "steam cracking -> ethylene/propylene/butadiene/pyrolysis gasoline/hydrogen"
    "BASF steam-cracker process description"
    "not assigned / not required for corporate process page"
    "process-page QID unresolved"
    "industrial/petrochemical process Dewey coordinate unresolved"
    "https://www.basf.com/global/en/who-we-are/organization/locations/europe/german-sites/ludwigshafen/the-site/production/the-production-verbund/Steamcracker"
    "primary operator description of a real steam-cracker product slate; not universal yield/kinetics authority"

chlorAlkaliRepoSource : ProcessSourceCoordinate
chlorAlkaliRepoSource =
  processSourceCoordinate
    "chloride oxidation + water reduction -> chlorine/hydrogen/hydroxide bookkeeping"
    "DASHI.Chemistry.ChlorAlkaliCanonicalHalfReactionsExact"
    "repository object; external DOI not used as same-object proof"
    "not applicable to repository object"
    "industrial electrochemistry catalogue coordinate unresolved"
    "DASHI/Chemistry/ChlorAlkaliCanonicalHalfReactionsExact.agda"
    "primary repo-native exact stoichiometric half-reaction object"

------------------------------------------------------------------------
-- Exact repo-native stoichiometric receipt is reused wholesale rather than
-- reproving equality of equality proofs.  Its own fields carry the exact
-- two-electron multiplicities at anode and cathode.
------------------------------------------------------------------------

chlorAlkaliHalfReactionPair : Half.CanonicalHalfReactionPair
chlorAlkaliHalfReactionPair = Half.canonicalHalfReactionPairReceipt

------------------------------------------------------------------------
-- Concrete industrial chain already owned elsewhere.
------------------------------------------------------------------------

hydrocarbonToEthyleneEdge : Industrial.IndustrialTransformationEdge
hydrocarbonToEthyleneEdge = Industrial.hydrocarbonToEthylene

chlorineEthyleneToEDCEdge : Industrial.IndustrialTransformationEdge
chlorineEthyleneToEDCEdge = Industrial.chlorineEthyleneToEDC

edcToVCMEdge : Industrial.IndustrialTransformationEdge
edcToVCMEdge = Industrial.edcToVCM

vcmToPVCEdge : Industrial.IndustrialTransformationEdge
vcmToPVCEdge = Industrial.vcmToPVC

------------------------------------------------------------------------
-- Same-object identity and promotion boundaries.
------------------------------------------------------------------------

record PetrochemicalAtomicIdentityBoundary : Set where
  constructor petrochemicalAtomicIdentityBoundary
  field
    atomicChlorineEqualsMolecularChlorine : Bool
    atomicChlorineEqualsMolecularChlorineIsFalse :
      atomicChlorineEqualsMolecularChlorine ≡ false

    atomicNumberDeterminesMolecularSpecies : Bool
    atomicNumberDeterminesMolecularSpeciesIsFalse :
      atomicNumberDeterminesMolecularSpecies ≡ false

    halfReactionStoichiometryDeterminesElectrodePotential : Bool
    halfReactionStoichiometryDeterminesElectrodePotentialIsFalse :
      halfReactionStoichiometryDeterminesElectrodePotential ≡ false

    electronMultiplicityDeterminesPlantCurrentEfficiency : Bool
    electronMultiplicityDeterminesPlantCurrentEfficiencyIsFalse :
      electronMultiplicityDeterminesPlantCurrentEfficiency ≡ false

    ethyleneIdentityDeterminesSteamCrackerYield : Bool
    ethyleneIdentityDeterminesSteamCrackerYieldIsFalse :
      ethyleneIdentityDeterminesSteamCrackerYield ≡ false

    molecularVCMIdentityDeterminesPVCGrade : Bool
    molecularVCMIdentityDeterminesPVCGradeIsFalse :
      molecularVCMIdentityDeterminesPVCGrade ≡ false

    sameNominalPVCDeterminesUniqueUpstreamCarbonAndChlorineHistory : Bool
    sameNominalPVCDeterminesUniqueUpstreamCarbonAndChlorineHistoryIsFalse :
      sameNominalPVCDeterminesUniqueUpstreamCarbonAndChlorineHistory ≡ false

canonicalPetrochemicalAtomicIdentityBoundary :
  PetrochemicalAtomicIdentityBoundary
canonicalPetrochemicalAtomicIdentityBoundary =
  petrochemicalAtomicIdentityBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Highest-alpha cross-pollination target.
------------------------------------------------------------------------

record PetrochemicalCrossPollinationFrontier : Set where
  constructor petrochemicalCrossPollinationFrontier
  field
    upstreamAtomicNeed : String
    firstMolecularNeed : String
    firstReactionNeed : String
    firstProcessNeed : String
    temporalNeed : String
    attributionNeed : String
    nextComputation : String

canonicalPetrochemicalCrossPollinationFrontier :
  PetrochemicalCrossPollinationFrontier
canonicalPetrochemicalCrossPollinationFrontier =
  petrochemicalCrossPollinationFrontier
    "recover element/charge/electronic-state identities without collapsing atoms into molecules"
    "derive or import same-object molecular electronic states for Cl2, ethylene, EDC and VCM, with geometry/bond/stereo/environment receipts"
    "attach reaction-energy and enablement witnesses to the existing chlorination/dehydrochlorination/polymerisation transitions before kinetic weighting"
    "retain cracker/chlor-alkali/EDC-VCM process envelopes, separation, safety, yield and quality as plant-level fibres"
    "carry feed, species, reaction and product states as fibres over time; same nominal product does not erase custody/process history"
    "for every snowballed object retain DOI/QID/PubChem/ChEBI/Dewey/direct-link/source-role fields; unresolved identifiers remain unresolved"
    "after Li/Be multi-orbital atomic state tracking, use a small-molecule electronic-structure producer as the next bridge rather than jumping directly from periodicity to petrochemical yields"

hyperfibreBoundary : Hyper.AtomicChemistryCrossPollinationBoundary
hyperfibreBoundary = Hyper.canonicalAtomicChemistryCrossPollinationBoundary
