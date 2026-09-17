module DASHI.Biology.Agriculture.AcaciaSenegalBNFMeasurementHierarchyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact as Nodulation
import DASHI.Biology.Agriculture.AcaciaSenegalBNFEdaphicLESExact as Edaphic
import DASHI.Biology.Agriculture.AcaciaSenegalPlantNitrogenAssimilationEvidenceExact as PlantN
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- ACACIA BNF MEASUREMENT HIERARCHY
--
-- "BNF evidence" is not one observation type. Gene identity, nodulation,
-- acetylene-reduction activity, foliar isotope/Ndfa and ecosystem soil-N
-- observations answer different consumer questions.
------------------------------------------------------------------------

bakhoum2015DOI : String
bakhoum2015DOI = "10.1007/s00248-014-0507-1"

githae2013DOI : String
githae2013DOI = PlantN.githae2013DOI

raddad2005DOI : String
raddad2005DOI = PlantN.raddad2005DOI

peerJ2018DOI : String
peerJ2018DOI = Edaphic.peerJ2018DOI

assefaKleiner1998DOI : String
assefaKleiner1998DOI = "10.1007/s003740050400"

assefaKleiner1998 : Attribution.AttributedSource
assefaKleiner1998 = Attribution.mkDOISource
  "Fassil Assefa; Dieter Kleiner"
  "Nodulation pattern and acetylene reduction (nitrogen fixation) activity of some highland and lowland Acacia species of Ethiopia"
  "Biology and Fertility of Soils 27(1):60-64"
  "1998"
  assefaKleiner1998DOI
  "https://doi.org/10.1007/s003740050400"
  Attribution.academicArticleSource
  "Multi-Acacia source including Acacia senegal; reports considerable variation in acetylene-reduction activity and no correlation between acetylene-reduction activity and plant nitrogen content in the studied species set."
  Attribution.publicAttribution

data BNFMeasurementRole : Set where
  symbioticGeneIdentity : BNFMeasurementRole
  noduleObservation : BNFMeasurementRole
  acetyleneReductionActivity : BNFMeasurementRole
  specificAcetyleneReductionActivity : BNFMeasurementRole
  foliarNaturalAbundance15N : BNFMeasurementRole
  nitrogenDerivedFromAtmosphereEstimate : BNFMeasurementRole
  plantNitrogenContent : BNFMeasurementRole
  soilNitrogenPoolOrFlux : BNFMeasurementRole

data BNFConsumerLevel : Set where
  geneticPotential : BNFConsumerLevel
  nodulationState : BNFConsumerLevel
  nitrogenaseActivityProxy : BNFConsumerLevel
  plantIntegratedFixedNContribution : BNFConsumerLevel
  ecosystemNitrogenOutcome : BNFConsumerLevel

record BNFMeasurementReceipt : Set where
  constructor bnf-measurement-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    measurementRole : BNFMeasurementRole
    nearestConsumerLevel : BNFConsumerLevel
    methodReading : String
    directMolecularFlux : Bool
    plantIntegratedEvidence : Bool
    ecosystemOutcomeEvidence : Bool
open BNFMeasurementReceipt public

bakhoumARAReceipt : BNFMeasurementReceipt
bakhoumARAReceipt = bnf-measurement-receipt
  (Nodulation.attributedSource Nodulation.bakhoum2015)
  bakhoum2015DOI
  acetyleneReductionActivity
  nitrogenaseActivityProxy
  "Acetylene-reduction activity retained as an enzyme/activity proxy in the reported Acacia inoculation-efficiency tests."
  false false false

bakhoumSARAReceipt : BNFMeasurementReceipt
bakhoumSARAReceipt = bnf-measurement-receipt
  (Nodulation.attributedSource Nodulation.bakhoum2015)
  bakhoum2015DOI
  specificAcetyleneReductionActivity
  nitrogenaseActivityProxy
  "Specific acetylene-reduction activity retained separately from total ARA, nodule count and plant-N integration."
  false false false

assefaKleinerARAReceipt : BNFMeasurementReceipt
assefaKleinerARAReceipt = bnf-measurement-receipt
  assefaKleiner1998
  assefaKleiner1998DOI
  acetyleneReductionActivity
  nitrogenaseActivityProxy
  "Acetylene-reduction activity in a multi-Acacia source including A. senegal; the source reports that ARA variation did not correlate with plant nitrogen content."
  false false false

isaacFoliarReceipt : BNFMeasurementReceipt
isaacFoliarReceipt = bnf-measurement-receipt
  Edaphic.isaacEtAl2011
  Edaphic.isaac2011DOI
  nitrogenDerivedFromAtmosphereEstimate
  plantIntegratedFixedNContribution
  "Foliar 15N natural-abundance based N2-fixation contribution estimate in natural Acacia populations."
  false true false

githaeFoliarReceipt : BNFMeasurementReceipt
githaeFoliarReceipt = bnf-measurement-receipt
  PlantN.githaeEtAl2013
  PlantN.githae2013DOI
  nitrogenDerivedFromAtmosphereEstimate
  plantIntegratedFixedNContribution
  "Leaf 15N natural-abundance fixation estimate across Acacia senegal varieties/sites; nodule assessment is separately observed."
  false true false

raddadFoliarReceipt : BNFMeasurementReceipt
raddadFoliarReceipt = bnf-measurement-receipt
  PlantN.raddadEtAl2005
  PlantN.raddad2005DOI
  nitrogenDerivedFromAtmosphereEstimate
  plantIntegratedFixedNContribution
  "Leaf 15N natural-abundance Ndfa estimate across eight Acacia senegal provenances and tree ages in Blue Nile Sudan; provenance and age remain indexed, and the source's foliage fixed-N contribution is retained as plant-level rather than direct molecular flux."
  false true false

peerJSoilNReceipt : BNFMeasurementReceipt
peerJSoilNReceipt = bnf-measurement-receipt
  Edaphic.abakerEtAlPeerJ2018
  peerJ2018DOI
  soilNitrogenPoolOrFlux
  ecosystemNitrogenOutcome
  "Soil N/fertility and foliar delta-15N evidence in Sudan plantations; source interpretation says N2 fixation was not an important contributor to plantation soil N in the studied system."
  false false true

------------------------------------------------------------------------
-- Canonical ladder remains untouched: proxy evidence is not generic closure.
------------------------------------------------------------------------

genericBacterialFixedNFluxRemainsOpen :
  Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
genericBacterialFixedNFluxRemainsOpen = refl

record BNFMeasurementBoundary : Set where
  constructor bnf-measurement-boundary
  field
    araEqualsDirectN2FixationRate : Bool
    araDeterminesPlantNitrogenContent : Bool
    saraEqualsIntegratedPlantFixedNDelivery : Bool
    noduleCountEqualsNitrogenaseActivity : Bool
    geneIdentityEqualsRealisedActivity : Bool
    foliarIsotopeEstimateEqualsDirectNitrogenaseFlux : Bool
    soilNPoolEqualsBNFContribution : Bool
    plantNdfaEqualsEcosystemSoilNOutcome : Bool
    activityProxyClosesGenericBacterialFixedNFlux : Bool
    measurementRoleMustRemainIndexed : Bool
    sourceAndMethodMustRemainIndexed : Bool
open BNFMeasurementBoundary public

canonicalMeasurementBoundary : BNFMeasurementBoundary
canonicalMeasurementBoundary = bnf-measurement-boundary
  false false false false false false false false false true true

attributionRule : String
attributionRule =
  "Bakhoum et al. 2015 (DOI 10.1007/s00248-014-0507-1; PMID 25315832) owns its Acacia nodulation/ARA/SARA propositions. Assefa & Kleiner 1998 (DOI 10.1007/s003740050400) owns its multi-Acacia ARA/plant-N non-correlation proposition; DASHI does not widen that statement beyond the studied source scope. Isaac et al. 2011 (DOI 10.1016/j.foreco.2010.11.011), Githae et al. 2013 (DOI 10.1080/15324982.2013.784377), Raddad et al. 2005 (DOI 10.1007/s11104-005-2152-4), and Abaker et al. 2018 (DOI 10.7717/peerj.5232; PMID 30018862; PMCID PMC6044267) own their distinct isotope/plant-N/soil-N propositions. DASHI owns the measurement-role hierarchy and no-substitution boundaries."
