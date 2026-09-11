module DASHI.Law.SensibLawWoogarooKoalaPopulationConnectivitySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- WOOGAROO KOALA POPULATION / CONNECTIVITY SNOWBALL
--
-- Highest-alpha follow from SensibLawWoogarooEvidenceDependencyMatrixExact.
-- Keep source identity, biological carrier identity, consumer payment and
-- library/entity navigation separate.
------------------------------------------------------------------------

qutCurrentSubmission : Attribution.AttributedSource
qutCurrentSubmission = Attribution.mkNoDOISource
  "Monica Taylor; Rowena Maguire; Bridget Lewis"
  "Submission re EPBC Case Referral 2019/8575 – Springview Village 2 & 3 (Woogaroo Forest)"
  "QUT School of Law submission to the Commonwealth Environment Minister"
  "2026"
  "https://img1.wsimg.com/blobby/go/c204ebbc-02bb-46d9-ad71-ed7d494e752a/QUT%20LTR%20EPBC%20referral%20Woogaroo%20-%2012032026.pdf"
  Attribution.institutionalSource
  "current project-specific legal/environmental submission; asks rejection for unacceptable impacts to EPBC-listed species and expressly aligns its ecological reasoning with Hugh Possingham and Christina Zdenek; does not itself apply Queensland NCA s 102"
  Attribution.publicAttribution

qccCurrentSubmission : Attribution.AttributedSource
qccCurrentSubmission = Attribution.mkNoDOISource
  "Anthony Gough / Queensland Conservation Council"
  "EPBC 2019/8575 submission: Springview Village Stages 2 and 3 - Woogaroo Creek Forest Landscape"
  "Queensland Conservation Council submission"
  "2026"
  "https://assets.nationbuilder.com/queenslandconservation/pages/4724/attachments/original/1773626602/QCC-Submission-EPBC-2019_8575-SpringviewVillage-Stages-2-3-WoogarooCreekForestLandscape.pdf"
  Attribution.institutionalSource
  "current independent project-specific ecological submission: records confirmed on-site koala activity, a resident population, Woogaroo Creek-Opossum Creek as a connected habitat network, and a fragmentation pathway to landscape-scale population viability; does not by itself prove NCA s 13 essentiality or s 102"
  Attribution.publicAttribution

leePopulationGenetics : Attribution.AttributedSource
leePopulationGenetics = Attribution.mkDOISource
  "Kristen E. Lee; Jennifer M. Seddon; Sean W. Corley; William A. H. Ellis; Stephen D. Johnston; Deidre L. de Villiers; Harriet J. Preece; Frank N. Carrick"
  "Genetic variation and structuring in the threatened koala populations of Southeast Queensland"
  "Conservation Genetics 11(6):2091-2103"
  "2010"
  "10.1007/s10592-009-9987-9"
  "https://doi.org/10.1007/s10592-009-9987-9"
  Attribution.academicArticleSource
  "primary population-genetics source: 512 koalas across ten mainland SEQ LGAs plus one island; six genetic clusters; major roads and rivers consistent with barriers to gene flow; regional population structure is not a site-specific Springview cluster assignment"
  Attribution.publicAttribution

timmsFowlerGeneFlow : Attribution.AttributedSource
timmsFowlerGeneFlow = Attribution.mkDOISource
  "P. Timms; E. V. Fowler"
  "Genetic diversity and gene flow among southeastern Queensland koalas (Phascolarctos cinereus)"
  "Molecular Ecology"
  "2000"
  "10.1046/j.1365-294x.2000.00844.x"
  "https://doi.org/10.1046/j.1365-294x.2000.00844.x"
  Attribution.academicArticleSource
  "primary genetic source over five SEQ populations; finds significant genetic heterogeneity among most populations and supports spatial structuring; does not identify the present Woogaroo/Springview population"
  Attribution.publicAttribution

tkaczynskiSEQReview : Attribution.AttributedSource
tkaczynskiSEQReview = Attribution.mkDOISource
  "Aaron Tkaczynski; Sharyn Rundle-Thiele"
  "Koala conservation in South East Queensland: A grey literature review analysis"
  "Conservation Science and Practice 5(3):e12874"
  "2023"
  "10.1111/csp2.12874"
  "https://doi.org/10.1111/csp2.12874"
  Attribution.academicArticleSource
  "SEQ-wide conservation review used as regional context; land clearing, urbanisation and habitat loss are regional threats; not a Springview population census"
  Attribution.publicAttribution

ipswichKoalaPlan : Attribution.AttributedSource
ipswichKoalaPlan = Attribution.mkNoDOISource
  "Ipswich City Council"
  "Koala Conservation and Habitat Management Plan"
  "Ipswich City Council"
  "2018"
  "https://www.ipswich.qld.gov.au/files/assets/public/v/1/about-council/initiatives/environment/wildlife/koala-conservation/documents/koala-conservation-plan.pdf"
  Attribution.governmentSource
  "local-government population/context source: records large Ipswich home ranges, landscape connectivity as important, and a conservative Ipswich estimate exceeding 4,000 animals based on Bussey and Ellis 2016; not an exact Springview population boundary or viability proof"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- QID / Dewey / external identity coordinates.
------------------------------------------------------------------------

record ExternalCoordinate : Set where
  constructor external-coordinate
  field
    label : String
    qid : String
    dewey : String
    verification : String
    identityCreatesEvidence : Bool
open ExternalCoordinate public

koalaCoordinate : ExternalCoordinate
koalaCoordinate = external-coordinate
  "koala / Phascolarctos cinereus"
  "Q36101"
  "unresolved: no exact inspected DDC promoted in this pass"
  "Wikidata taxon identity inspected 2026-09-11"
  false

habitatFragmentationCoordinate : ExternalCoordinate
habitatFragmentationCoordinate = external-coordinate
  "habitat fragmentation"
  "Q913302"
  "unresolved: no exact inspected DDC promoted in this pass"
  "Wikidata concept identity inspected 2026-09-11"
  false

conservationBiologyCoordinate : ExternalCoordinate
conservationBiologyCoordinate = external-coordinate
  "conservation biology"
  "Q641498"
  "unresolved: no exact inspected DDC promoted in this pass"
  "Wikidata concept identity inspected 2026-09-11"
  false

------------------------------------------------------------------------
-- Population-scale carrier ladder.
------------------------------------------------------------------------

data PopulationScale : Set where
  southeastQueenslandRegional
  ipswichLocalGovernmentArea
  woogarooCreekLandscape
  springviewReferralSite
  independentlyGenotypedCluster : PopulationScale

record PopulationConnectivityReceipt : Set where
  constructor population-connectivity-receipt
  field
    seqPopulationStructurePaid : Bool
    seqSixGeneticClustersPaid : Bool
    urbanFragmentationGeneFlowRiskPaid : Bool
    ipswichPopulationPresencePaid : Bool
    ipswichPopulationEstimatePaid : Bool
    woogarooResidentKoalaPresencePaid : Bool
    woogarooConnectedHabitatNetworkPaid : Bool
    projectFragmentationViabilityOpinionPaid : Bool
    exactSpringviewGeneticClusterPaid : Bool
    exactSpringviewViablePopulationBoundaryPaid : Bool
    noSiteCounterfactualQuantified : Bool
    statutoryS13EssentialityPaid : Bool
    statutoryS102EffectPaid : Bool
open PopulationConnectivityReceipt public

currentPopulationConnectivityReceipt : PopulationConnectivityReceipt
currentPopulationConnectivityReceipt = population-connectivity-receipt
  true true true true true true true true false false false false false

------------------------------------------------------------------------
-- The investigation has therefore moved the population residual.
--
-- OLD: identify a viable Koala population independently of the development.
-- NEW: regional/local population existence and structure are source-paid;
--      identify which independently characterised cluster/subpopulation the
--      Springview/Woogaroo animals belong to, then quantify loss of persistence,
--      movement, breeding/dispersal and resource access under site severance.
------------------------------------------------------------------------

firstUnpaidPopulationIdentity : String
firstUnpaidPopulationIdentity =
  "same-object join: Springview/Woogaroo resident koalas <-> independently characterised SEQ genetic/demographic cluster or subpopulation"

firstUnpaidS13QuantitativeConsumer : String
firstUnpaidS13QuantitativeConsumer =
  "counterfactual delta under removal/severance of the exact approved site: persistence, movement/connectivity, breeding/dispersal, resource access"

firstUnpaidS102Consumer : String
firstUnpaidS102Consumer =
  "apply current independent project-specific ecological evidence to the exact Queensland NCA s 102 threatening-process / likely-significant-detrimental-effect consumer"

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data SEQPopulationMeansSpringviewCluster : Set where
data IpswichEstimateMeansSitePopulation : Set where
data ConnectedHabitatMeansStatutoryEssentiality : Set where
data EPBCImpactOpinionMeansNcaS102 : Set where
data QidMeansPopulationIdentity : Set where
data DoiMeansClaimPaid : Set where

data CurrentSubmissionMeansIndependentFieldSurvey : Set where

seqPopulationDoesNotIdentifySpringviewCluster : SEQPopulationMeansSpringviewCluster → ⊥
seqPopulationDoesNotIdentifySpringviewCluster ()

ipswichEstimateDoesNotIdentifySitePopulation : IpswichEstimateMeansSitePopulation → ⊥
ipswichEstimateDoesNotIdentifySitePopulation ()

connectedHabitatDoesNotCreateS13Essentiality : ConnectedHabitatMeansStatutoryEssentiality → ⊥
connectedHabitatDoesNotCreateS13Essentiality ()

epbcOpinionDoesNotCreateNcaS102 : EPBCImpactOpinionMeansNcaS102 → ⊥
epbcOpinionDoesNotCreateNcaS102 ()

qidDoesNotCreatePopulationIdentity : QidMeansPopulationIdentity → ⊥
qidDoesNotCreatePopulationIdentity ()

doiDoesNotPayClaim : DoiMeansClaimPaid → ⊥
doiDoesNotPayClaim ()

submissionDoesNotBecomeFieldSurvey : CurrentSubmissionMeansIndependentFieldSurvey → ⊥
submissionDoesNotBecomeFieldSurvey ()

record WoogarooPopulationSnowballBoundary : Set where
  constructor woogaroo-population-snowball-boundary
  field
    primaryAndPeerReviewedSourcesSeparated : Bool
    doiQidDeweyLinksTravel : Bool
    currentProjectOpinionNowLocated : Bool
    currentProjectOpinionPaysNcaS102 : Bool
    regionalPopulationStructureNowPaid : Bool
    exactSiteClusterIdentityPaid : Bool
    exactSiteViabilityCounterfactualPaid : Bool
    s13Paid : Bool
open WoogarooPopulationSnowballBoundary public

canonicalWoogarooPopulationSnowballBoundary : WoogarooPopulationSnowballBoundary
canonicalWoogarooPopulationSnowballBoundary =
  woogaroo-population-snowball-boundary true true true false true false false false
