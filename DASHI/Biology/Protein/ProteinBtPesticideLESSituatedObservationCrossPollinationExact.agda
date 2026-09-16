module DASHI.Biology.Protein.ProteinBtPesticideLESSituatedObservationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Protein
import DASHI.Wikimedia.IbrahimCannabisBtBiopesticideExposureParetoExact as Bt
import DASHI.Wikimedia.IbrahimPesticideExperimentDesignParetoExact as Pesticide
import DASHI.Environment.LESDomainBasisBidiFrontierExact as LES
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as SituatedLES

------------------------------------------------------------------------
-- PROTEIN / Bt / PESTICIDE / LES SITUATED-OBSERVATION CROSS-POLLINATION
--
-- This owner reuses four existing repository surfaces rather than inventing a
-- pesticide, protein or LES ontology:
--
--   * ProteinSituatedHyperfabricExact:
--       protein identity is a query-relative projection and assay/context/
--       history/provenance may be required by a declared protein consumer;
--   * IbrahimCannabisBtBiopesticideExposureParetoExact:
--       generic Bt is a composite exposure family, not one small molecule;
--       spores, strain identity and Cry/Vip proteins require distinct observers;
--   * IbrahimPesticideExperimentDesignParetoExact:
--       observer collisions justify the smallest discriminating experiment;
--   * LESDomainBasisBidiFrontierExact / LESSituatedSocioEcologicalHyperfabricExact:
--       chemistry, hydrology/transport, ecology, history and provenance remain
--       distinct domain/observation coordinates.
--
-- The exact finite non-factorability witnesses below are DASHI synthesis.
-- They do not attribute the generic theorem to the Bt, pesticide or LES source
-- literature and do not transfer mechanisms between TRPA1, AdK, Cry/Vip or any
-- pesticide target organism.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Existing donor surfaces.
------------------------------------------------------------------------

proteinSituatedBoundary : Protein.ProteinSituatedHyperfabricBoundary
proteinSituatedBoundary = Protein.canonicalProteinSituatedHyperfabricBoundary

btOntologyBoundary : Bt.BtOntologyBoundary
btOntologyBoundary = Bt.canonicalBtOntologyBoundary

btCoverageBoundary : Bt.BtCoverageBoundary
btCoverageBoundary = Bt.canonicalBtCoverageBoundary

btExposureBoundary : Bt.BtExposureBoundary
btExposureBoundary = Bt.canonicalBtExposureBoundary

btObserverCollision : Pesticide.ObserverCollision
btObserverCollision = Pesticide.btCollision

glyphosateObserverCollision : Pesticide.ObserverCollision
glyphosateObserverCollision = Pesticide.glyphosateCollision

pesticideExperimentBoundary : Pesticide.PesticideExperimentDesignBoundary
pesticideExperimentBoundary = Pesticide.canonicalPesticideExperimentDesignBoundary

lesDomainBoundary : LES.LESDomainBasisBoundary
lesDomainBoundary = LES.canonicalLESDomainBasisBoundary

lesSituatedBoundary : SituatedLES.LESSituatedSocioEcologicalBoundary
lesSituatedBoundary = SituatedLES.canonicalLESSituatedSocioEcologicalBoundary

btCryProteinObservationCandidate : Bt.BtObservationAdmission
btCryProteinObservationCandidate = Bt.cryProteinCandidate

btStrainObservationCandidate : Bt.BtObservationAdmission
btStrainObservationCandidate = Bt.btkSporePCRCandidate

lesChemistryBasis : LES.ForwardDomainBasis
lesChemistryBasis = LES.chemistryForwardBasis

lesPlantEcologyBasis : LES.ForwardDomainBasis
lesPlantEcologyBasis = LES.plantForwardBasis

lesHydrologyTransportBasis : LES.ForwardDomainBasis
lesHydrologyTransportBasis = LES.hydrologyTransportForwardBasis

lesTrophicBasis : LES.ForwardDomainBasis
lesTrophicBasis = LES.trophicForwardBasis

------------------------------------------------------------------------
-- 2. Coarse pesticide/Bt naming does not determine the required observer.
--
-- This finite witness is structural.  It does not say these are the only
-- pesticide object classes or assays.  It instantiates the already-owned Bt
-- distinction between viable/strain material, Cry/Vip protein and ordinary
-- small-molecule pesticide chemistry.
------------------------------------------------------------------------

data AgrochemicalObservationWorld : Set where
  btStrainWorld : AgrochemicalObservationWorld
  btCryProteinWorld : AgrochemicalObservationWorld
  glyphosateWorld : AgrochemicalObservationWorld

data CoarsePesticideToken : Set where
  pesticideOrBiopesticidePresent : CoarsePesticideToken

data RequiredObservationFamily : Set where
  organismOrStrainObserver : RequiredObservationFamily
  proteinObserver : RequiredObservationFamily
  dedicatedPolarAnalyteObserver : RequiredObservationFamily

coarsePesticideObservation : AgrochemicalObservationWorld → CoarsePesticideToken
coarsePesticideObservation _ = pesticideOrBiopesticidePresent

requiredObservationFamily : AgrochemicalObservationWorld → RequiredObservationFamily
requiredObservationFamily btStrainWorld = organismOrStrainObserver
requiredObservationFamily btCryProteinWorld = proteinObserver
requiredObservationFamily glyphosateWorld = dedicatedPolarAnalyteObserver

btStrainVsProteinNeedDiffer :
  requiredObservationFamily btStrainWorld ≡
  requiredObservationFamily btCryProteinWorld → ⊥
btStrainVsProteinNeedDiffer ()

btProteinVsGlyphosateNeedDiffer :
  requiredObservationFamily btCryProteinWorld ≡
  requiredObservationFamily glyphosateWorld → ⊥
btProteinVsGlyphosateNeedDiffer ()

coarsePesticideTokenCannotDetermineObserver :
  INF.FactorsThrough coarsePesticideObservation requiredObservationFamily → ⊥
coarsePesticideTokenCannotDetermineObserver =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      btStrainWorld
      btCryProteinWorld
      refl
      btStrainVsProteinNeedDiffer)

------------------------------------------------------------------------
-- 3. Pesticide identity alone does not determine which LES domain socket is
-- required by the declared consumer.
--
-- These are repository-local consumer worlds, not empirical claims that a
-- particular pesticide necessarily occupies each environmental pathway.
------------------------------------------------------------------------

data LESExposureConsumerWorld : Set where
  chemistryConsumerWorld : LESExposureConsumerWorld
  plantInteractionConsumerWorld : LESExposureConsumerWorld
  hydrologyTransportConsumerWorld : LESExposureConsumerWorld
  trophicInteractionConsumerWorld : LESExposureConsumerWorld

data SamePesticideIdentity : Set where
  retainedSamePesticideIdentity : SamePesticideIdentity

pesticideIdentityProjection : LESExposureConsumerWorld → SamePesticideIdentity
pesticideIdentityProjection _ = retainedSamePesticideIdentity

requiredLESDomain : LESExposureConsumerWorld → LES.EnvironmentalDomain
requiredLESDomain chemistryConsumerWorld = LES.chemistry
requiredLESDomain plantInteractionConsumerWorld = LES.plantEcology
requiredLESDomain hydrologyTransportConsumerWorld = LES.hydrologyTransport
requiredLESDomain trophicInteractionConsumerWorld = LES.trophicEcology

chemistryVsHydrologyDomainDiffer :
  requiredLESDomain chemistryConsumerWorld ≡
  requiredLESDomain hydrologyTransportConsumerWorld → ⊥
chemistryVsHydrologyDomainDiffer ()

pesticideIdentityCannotDetermineLESDomain :
  INF.FactorsThrough pesticideIdentityProjection requiredLESDomain → ⊥
pesticideIdentityCannotDetermineLESDomain =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      chemistryConsumerWorld
      hydrologyTransportConsumerWorld
      refl
      chemistryVsHydrologyDomainDiffer)

------------------------------------------------------------------------
-- 4. Cross-domain interpretation.
------------------------------------------------------------------------

record SituatedAgrochemicalObservation : Set where
  constructor situated-agrochemical-observation
  field
    objectIdentity : String
    objectRole : String
    matrixOrSite : String
    timeOrHistory : String
    routeOrTransportContext : String
    observerOrAssay : String
    environmentalDomain : LES.EnvironmentalDomain
    sourceAndProvenance : String
open SituatedAgrochemicalObservation public

btCrySituatedObservationShape : SituatedAgrochemicalObservation
btCrySituatedObservationShape = situated-agrochemical-observation
  "exact Bt product/strain/Cry-or-Vip identity required"
  "protein exposure object inside a larger microbial/formulation preparation"
  "matrix/site must be retained; generic cannabis/environment token is insufficient"
  "application-to-sampling history retained"
  "surface/residue/thermal/aerosol/ecological transport route must be declared by the consumer"
  "protein assay/proteomics candidate only after protein identity is fixed"
  LES.chemistry
  "retain product label + strain/protein identity + source role; identifiers do not create exposure or effect"

------------------------------------------------------------------------
-- 5. WrongType / attribution firewalls.
------------------------------------------------------------------------

data BtCryProteinCreatesTRPA1Mechanism : Set where
data BtCryProteinCreatesAdKMechanism : Set where
data PesticideIdentityCreatesEcologicalEffect : Set where
data QidOrDoiCreatesPesticideMechanism : Set where
data CrossPollinationTransfersSourceAuthority : Set where
data SameProteinCategoryCreatesSameBiologicalObject : Set where

data LESDomainVocabularyCreatesMechanisticFateModel : Set where

btCryProteinDoesNotCreateTRPA1Mechanism : BtCryProteinCreatesTRPA1Mechanism → ⊥
btCryProteinDoesNotCreateTRPA1Mechanism ()

btCryProteinDoesNotCreateAdKMechanism : BtCryProteinCreatesAdKMechanism → ⊥
btCryProteinDoesNotCreateAdKMechanism ()

pesticideIdentityDoesNotCreateEcologicalEffect : PesticideIdentityCreatesEcologicalEffect → ⊥
pesticideIdentityDoesNotCreateEcologicalEffect ()

qidOrDoiDoesNotCreatePesticideMechanism : QidOrDoiCreatesPesticideMechanism → ⊥
qidOrDoiDoesNotCreatePesticideMechanism ()

crossPollinationDoesNotTransferSourceAuthority : CrossPollinationTransfersSourceAuthority → ⊥
crossPollinationDoesNotTransferSourceAuthority ()

sameProteinCategoryDoesNotCreateSameBiologicalObject : SameProteinCategoryCreatesSameBiologicalObject → ⊥
sameProteinCategoryDoesNotCreateSameBiologicalObject ()

lesVocabularyDoesNotCreateMechanisticFateModel : LESDomainVocabularyCreatesMechanisticFateModel → ⊥
lesVocabularyDoesNotCreateMechanisticFateModel ()

------------------------------------------------------------------------
-- 6. Attribution rule.
------------------------------------------------------------------------

attributionRule : String
attributionRule =
  "Bt, pesticide-regulatory/assay and LES donors retain ownership only of their source-bounded domain premises. DOI/QID/PMID/PMCID/PDB/UniProt/product/strain/compound identifiers are provenance coordinates, not mechanism or effect authority. The non-factorability witnesses and cross-domain situated-observation bridge are DASHI synthesis. Reuse transfers structure only; it does not transfer authorship, toxicology, ecological effect, protein mechanism, legal authority or empirical validation."

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

record ProteinBtPesticideLESBoundary : Set where
  constructor protein-bt-pesticide-les-boundary
  field
    reusesProteinSituatedHyperfabric : Bool
    reusesBtObjectAndObserverSeparation : Bool
    reusesPesticideExperimentCollision : Bool
    reusesLESDomainBasis : Bool
    reusesLESSituatedProvenanceBoundary : Bool
    btGenericTokenIsCompleteExposureObject : Bool
    coarsePesticideTokenDeterminesObserver : Bool
    proteinIdentityIsCompletePredictiveState : Bool
    pesticideIdentityDeterminesLESDomain : Bool
    btCryProteinCreatesTRPA1Mechanism : Bool
    btCryProteinCreatesAdKMechanism : Bool
    pesticideIdentityCreatesEcologicalEffect : Bool
    lesDomainVocabularyCreatesMechanisticFateModel : Bool
    qidOrDoiCreatesPesticideMechanism : Bool
    crossPollinationTransfersSourceAuthority : Bool
open ProteinBtPesticideLESBoundary public

canonicalProteinBtPesticideLESBoundary : ProteinBtPesticideLESBoundary
canonicalProteinBtPesticideLESBoundary =
  protein-bt-pesticide-les-boundary
    true true true true true
    false false false false false false false false false false
