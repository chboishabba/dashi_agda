module DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- ACACIA / SENEGALIA SENEGAL RHIZOBIAL-BNF SOURCE ATLAS
--
-- Attribution rule:
--   source identity != source proposition != DASHI reconstruction
--   != DASHI finite collision != cross-source synthesis != deployment authority.
--
-- DOI metadata is carried by the canonical AttributedSource core. PMID/PMCID
-- are retained separately when verified.  Missing identifiers are represented
-- explicitly as "not recorded by atlas"; no identifier is guessed.
------------------------------------------------------------------------

data HostNameForm : Set where
  acaciaSenegalName : HostNameForm
  senegaliaSenegalName : HostNameForm

data AcaciaBNFSourceRole : Set where
  rootNodulatorDiversity : AcaciaBNFSourceRole
  matureTreeInoculation : AcaciaBNFSourceRole
  gumYieldInoculation : AcaciaBNFSourceRole
  rhizosphereSeasonality : AcaciaBNFSourceRole

data MeasurementFamily : Set where
  phenotypeGenotype : MeasurementFamily
  soilMicrobialMineralN : MeasurementFamily
  gumProduction : MeasurementFamily
  communityComposition : MeasurementFamily

record ExternalIdentifiers : Set where
  constructor external-identifiers
  field
    pmid : String
    pmcid : String
    taxonIdentity : String
open ExternalIdentifiers public

record AcaciaBNFSource : Set where
  constructor acacia-bnf-source
  field
    attributedSource : Attribution.AttributedSource
    identifiers : ExternalIdentifiers
    hostName : HostNameForm
    role : AcaciaBNFSourceRole
    measurement : MeasurementFamily
    site : String
    rhizobialIdentityReading : String
    boundedReading : String
    excludedPromotion : String
open AcaciaBNFSource public

fall2008 : AcaciaBNFSource
fall2008 = acacia-bnf-source
  (Attribution.mkDOISource
    "Dioumacor Fall; Diegane Diouf; M. Ourarhi; A. Faye; H. Abdelmounen; M. Neyra; S. N. Sylla; M. Missbah El Idrissi"
    "Phenotypic and genotypic characteristics of Acacia senegal (L.) Willd. root-nodulating bacteria isolated from soils in the dryland part of Senegal"
    "Letters in Applied Microbiology 47(2):85-97"
    "2008"
    "10.1111/j.1472-765X.2008.02389.x"
    "https://pubmed.ncbi.nlm.nih.gov/18565139/"
    Attribution.academicArticleSource
    "Primary source for diversity and stress-tolerance characteristics of A. senegal root-nodulating bacterial isolates; does not own DASHI factorisation or promotion firewalls."
    Attribution.publicAttribution)
  (external-identifiers "18565139" "not recorded by atlas" "host taxon identifier not promoted by this atlas")
  acaciaSenegalName
  rootNodulatorDiversity
  phenotypeGenotype
  "Dryland Senegal; soils surrounding Acacia senegal trees"
  "Source reports high phenotypic/genotypic diversity of root-nodulating bacteria and stress-adaptation phenotypes including heat, drought and salinity tolerance."
  "Supports host-associated root-nodulator diversity and stress-tolerance observations in the sampled system."
  "Root-nodulator identity, nif-related identity, or stress tolerance alone does not establish active nitrogenase, fixation rate, plant N delivery, soil-N outcome or deployment authority."

fall2016 : AcaciaBNFSource
fall2016 = acacia-bnf-source
  (Attribution.mkDOISource
    "Dioumacor Fall; Niokhor Bakhoum; Saidou Nourou Sall; Alzouma Mayaki Zoubeirou; Samba N. Sylla; Diegane Diouf"
    "Rhizobial Inoculation Increases Soil Microbial Functioning and Gum Arabic Production of 13-Year-Old Senegalia senegal (L.) Britton, Trees in the North Part of Senegal"
    "Frontiers in Plant Science 7:1355"
    "2016"
    "10.3389/fpls.2016.01355"
    "https://pubmed.ncbi.nlm.nih.gov/27656192/"
    Attribution.academicArticleSource
    "Primary mature-tree inoculation study; source owns only the measured study-specific outcomes, not a universal inoculation or nitrogenase-mechanism theorem."
    Attribution.publicAttribution)
  (external-identifiers "27656192" "PMC5013129" "host taxon identifier not promoted by this atlas")
  senegaliaSenegalName
  matureTreeInoculation
  soilMicrobialMineralN
  "Northern Senegal; 13-year-old Senegalia senegal trees"
  "Rhizobial inoculation treatment with soil microbial/mineral-N and gum-production measurements in the source study."
  "Supports source-bounded inoculation-associated changes in measured soil microbial functioning/mineral-N coordinates and gum production for the studied trees/site/window."
  "Does not establish that every observed effect is nitrogenase-mediated, that inoculation is universally beneficial, that fixation rate is known, or that another site should deploy the intervention."

faye2006 : AcaciaBNFSource
faye2006 = acacia-bnf-source
  (Attribution.mkDOISource
    "A. Faye; A. Sarr; D. Lesueur"
    "Effect of inoculation with rhizobia on the gum-arabic production of 10-year-old Acacia senegal trees"
    "Arid Land Research and Management 20(1):79-85"
    "2006"
    "10.1080/15324980500369475"
    "https://publications.cirad.fr/une_notice.php?dk=536263"
    Attribution.academicArticleSource
    "Primary mature-tree inoculation/gum-yield study; gum response is retained as its measured consumer and is not relabelled as direct BNF flux."
    Attribution.publicAttribution)
  (external-identifiers "not recorded by atlas" "not recorded by atlas" "host taxon identifier not promoted by this atlas")
  acaciaSenegalName
  gumYieldInoculation
  gumProduction
  "Rotto, Linguere Department, Senegal; 10-year-old Acacia senegal plantation"
  "Source inoculated mature trees with selected rhizobial strains and measured gum-arabic yield under the reported field protocol."
  "Supports the study-specific inoculation/gum-production comparison."
  "Gum-yield response is not a direct nitrogen-fixation-rate measurement and does not establish plant N balance, ecosystem N gain or universal field benefit."

herrmann2012 : AcaciaBNFSource
herrmann2012 = acacia-bnf-source
  (Attribution.mkDOISource
    "Laetitia Herrmann; Kadidia B. Sanon; Alzouma Mayaki Zoubeirou; Mahamadi Dianda; S. Sall; M. Thuita; D. Lesueur"
    "Seasonal changes of bacterial communities in the rhizosphere of Acacia senegal mature trees inoculated with Ensifer strains in Burkina Faso and Niger"
    "Agriculture, Ecosystems and Environment 157:47-53"
    "2012"
    "10.1016/j.agee.2011.12.014"
    "https://publications.cirad.fr/une_notice.php?dk=564796"
    Attribution.academicArticleSource
    "Primary seasonal/site rhizosphere-community study; source owns its measured community/soil coordinates, not active-fixation proof."
    Attribution.publicAttribution)
  (external-identifiers "not recorded by atlas" "not recorded by atlas" "host taxon identifier not promoted by this atlas")
  acaciaSenegalName
  rhizosphereSeasonality
  communityComposition
  "Mature-tree sites in Burkina Faso and Niger; dry/rainy seasons sampled 2006-2008"
  "Host-specific Ensifer inoculation context with total microbial biomass, soil inorganic nitrogen and 16S-rDNA community measurements."
  "Supports season/site/inoculation-indexed rhizosphere community and soil-coordinate observations."
  "Community change, inorganic-N observation, or Ensifer identity alone does not prove effective nodule fixation, integrated plant N delivery or a portable deployment rule."

canonicalAcaciaSources : List AcaciaBNFSource
canonicalAcaciaSources = fall2008 ∷ fall2016 ∷ faye2006 ∷ herrmann2012 ∷ []

acaciaAttributedAtlas : Attribution.AttributedSourceAtlas
acaciaAttributedAtlas = Attribution.mkSourceAtlas
  "Acacia/Senegalia senegal rhizobial BNF source atlas"
  "DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasExact"
  (attributedSource fall2008 ∷ attributedSource fall2016 ∷ attributedSource faye2006 ∷ attributedSource herrmann2012 ∷ [])
  "Source-bounded Acacia/Senegalia root-nodulator, mature-tree inoculation, gum-production and rhizosphere-context evidence; source identity does not promote active fixation or intervention authority."

record AcaciaSourceBoundary : Set where
  constructor acacia-source-boundary
  field
    hostSynonymImpliesSameStudy : Bool
    rhizobialIdentityImpliesEffectiveFixedNFlux : Bool
    inoculationResponseImpliesNitrogenaseMediation : Bool
    gumYieldResponseIsDirectFixationRate : Bool
    localFieldResultImpliesDeploymentAuthority : Bool
open AcaciaSourceBoundary public

canonicalAcaciaSourceBoundary : AcaciaSourceBoundary
canonicalAcaciaSourceBoundary = acacia-source-boundary false false false false false

hostSynonymDoesNotCollapseStudyIdentity :
  hostSynonymImpliesSameStudy canonicalAcaciaSourceBoundary ≡ false
hostSynonymDoesNotCollapseStudyIdentity = refl

rhizobialIdentityDoesNotCreateFixedNFlux :
  rhizobialIdentityImpliesEffectiveFixedNFlux canonicalAcaciaSourceBoundary ≡ false
rhizobialIdentityDoesNotCreateFixedNFlux = refl

attributionRule : String
attributionRule =
  "Each external paper owns only its source-bounded proposition. DOI/PMID/PMCID identify sources; Acacia/Senegalia naming identifies the host naming used by that source. DASHI owns the atlas typing, no-promotion boundaries and any later finite non-factorability theorem."
