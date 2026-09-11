module DASHI.Law.SensibLawWoogarooKoalaEvidenceSnowballIdentifierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Entity
import DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact as S102
import DASHI.Law.SensibLawWoogarooS13EssentialityStressTestExact as S13

------------------------------------------------------------------------
-- WOOGAROO KOALA EVIDENCE SNOWBALL — IDENTIFIERS / SOURCE ROLES
--
-- Ibrahim-style acquisition metadata for the live s 102 / s 13 consumers.
-- DOI, QID and Dewey are discovery/identity/classification coordinates only.
-- They do not manufacture source independence, same-object identity, legal
-- authority, ecological truth, statutory satisfaction or adjudication.
------------------------------------------------------------------------

data SourceLayer : Set where
  primaryLaw
  primaryGovernmentEcology
  primaryLocalGovernmentContext
  peerReviewedMechanism
  projectSpecificConsultant
  currentIndependentExpert : SourceLayer

data IdentifierState : Set where
  verified : IdentifierState
  unresolved : IdentifierState
  notApplicable : IdentifierState

record SnowballIdentifierReceipt : Set where
  constructor snowball-identifier-receipt
  field
    canonicalTitle : String
    authorOrIssuer : String
    year : String
    layer : SourceLayer
    doiState : IdentifierState
    doi : String
    qidState : IdentifierState
    qid : String
    deweyState : IdentifierState
    dewey : String
    primaryOrSecondary : String
    exactUse : String
    sourceIndependenceUse : String
    nextSnowballEdge : String
    promotionBoundary : String

open SnowballIdentifierReceipt public

nca102Receipt : SnowballIdentifierReceipt
nca102Receipt = snowball-identifier-receipt
  "Nature Conservation Act 1992 — ss 12, 102–105"
  "Queensland Parliamentary Counsel"
  "2026 current compilation"
  primaryLaw
  notApplicable ""
  unresolved "no publication/item QID safely resolved; statute identity remains title/jurisdiction/version"
  unresolved "Queensland-law Dewey coordinate not source-paid; do not invent"
  "primary statutory source"
  "Pays the legal wording: threatening process; likely significant detrimental effect; off-site order capacity; order duration."
  "Legally independent from the ecological evidence, but not ecological corroboration."
  "Search administration/history for actual interim conservation orders and procedural practice."
  "Statute text does not establish that Woogaroo facts satisfy s 102."

koalaEntityReceipt : SnowballIdentifierReceipt
koalaEntityReceipt = snowball-identifier-receipt
  "Koala / Phascolarctos cinereus"
  "taxon identity coordinate"
  "current"
  primaryGovernmentEcology
  notApplicable ""
  verified "Q36101"
  verified "599.25"
  "external entity/classification coordinate"
  "QID fixes the taxon entity; Dewey 599.25 is a mammal/koala discovery coordinate, not legal evidence."
  "Does not independently establish local occurrence, population identity or habitat essentiality."
  "Keep species status, occurrence, population and habitat-function carriers separate."
  "QID/Dewey identity is not species-status authority or project-specific evidence."

ipswichKoalaPlanReceipt : SnowballIdentifierReceipt
ipswichKoalaPlanReceipt = snowball-identifier-receipt
  "Koala Conservation and Habitat Management Plan"
  "Ipswich City Council"
  "current public plan"
  primaryLocalGovernmentContext
  notApplicable ""
  verified "Q1631867"
  unresolved "no publication-specific Dewey coordinate source-paid"
  "primary local-government ecological/management source"
  "Records that Ipswich koalas are regionally important, that habitat loss/fragmentation and road mortality are major threats, and that linear connectivity is a management concern."
  "Institutionally independent from SHG, but it is regional context rather than a same-project field replication."
  "Follow cited Ipswich population/genetics studies and identify the population unit relevant to Springfield/Woogaroo."
  "Regional Council strategy does not prove Springview habitat is essential under s 13 or that s 102 is satisfied."

ipswichCatchmentReceipt : SnowballIdentifierReceipt
ipswichCatchmentReceipt = snowball-identifier-receipt
  "Brisbane River Catchment — Woogaroo Creek including Mountain and Opossum creeks"
  "Ipswich City Council"
  "current public catchment description"
  primaryLocalGovernmentContext
  notApplicable ""
  verified "Q1631867"
  unresolved "no publication-specific Dewey coordinate source-paid"
  "primary local-government landscape source"
  "Records Woogaroo/Opossum in the same catchment, significant bushland in the upper catchment, importance for securing urban koala populations, and Flinders–Karawatha corridor context."
  "Independent landscape/government source, but not a direct Springview population viability study."
  "Join exact project geometry to the Council/State corridor and population-management surfaces."
  "Landscape importance does not itself establish statutory essentiality."

mcalpineBioconReceipt : SnowballIdentifierReceipt
mcalpineBioconReceipt = snowball-identifier-receipt
  "The importance of forest area and configuration relative to local habitat factors for conserving forest mammals: A case study of koalas in Queensland, Australia"
  "Clive A. McAlpine; Jonathan R. Rhodes; John G. Callaghan; Michiala E. Bowen; Daniel Lunney; David L. Mitchell; David V. Pullar; Hugh P. Possingham"
  "2006"
  peerReviewedMechanism
  verified "10.1016/j.biocon.2006.03.021"
  unresolved "publication QID not safely resolved in this audit"
  verified "577.27"
  "peer-reviewed mechanism/background source"
  "Supports the general mechanism that forest area/configuration and roads matter to koala occurrence in fragmented rural–urban SEQ landscapes. Dewey 577.27 is used as the habitat-fragmentation/landscape-change discovery coordinate, not as publication identity."
  "Independent from SHG; still not same-project evidence."
  "Use only as mechanism support for fragmentation/connectivity questions asked of a current expert."
  "General SEQ evidence cannot be promoted to a Woogaroo-specific effect magnitude."

mcalpineAustralReceipt : SnowballIdentifierReceipt
mcalpineAustralReceipt = snowball-identifier-receipt
  "Testing alternative models for the conservation of koalas in fragmented rural–urban landscapes"
  "Clive A. McAlpine; Michiala E. Bowen; John G. Callaghan; Daniel Lunney; Jonathan R. Rhodes; David L. Mitchell; David V. Pullar; Hugh P. Possingham"
  "2006"
  peerReviewedMechanism
  verified "10.1111/j.1442-9993.2006.01603.x"
  unresolved "publication QID not safely resolved in this audit"
  verified "577.27"
  "peer-reviewed mechanism/background source"
  "Supports a multilevel landscape model in which habitat amount, patch configuration, neighbourhood effects and sealed roads contribute to koala occurrence."
  "Independent from SHG; overlaps author/method lineage with the companion 2006 landscape work and therefore is not counted as a wholly independent scientific tradition."
  "Snowball to the cited/forward-citing koala connectivity literature, retaining author-lineage dependence."
  "Multiple papers from overlapping authors do not equal multiple independent Woogaroo observations."

rhodesDistributionReceipt : SnowballIdentifierReceipt
rhodesDistributionReceipt = snowball-identifier-receipt
  "Modeling species' distributions to improve conservation in semiurban landscapes: koala case study"
  "Jonathan R. Rhodes; Thorsten Wiegand; Clive A. McAlpine; John Callaghan; Daniel Lunney; Michiala Bowen; Hugh P. Possingham"
  "2006"
  peerReviewedMechanism
  verified "10.1111/j.1523-1739.2006.00330.x"
  unresolved "publication QID not safely resolved in this audit"
  verified "577.27"
  "peer-reviewed mechanism/background source"
  "Supports landscape-scale koala distribution modelling in a semiurban setting."
  "Partly overlapping author lineage with McAlpine/Rhodes papers; do not count as independent project observations."
  "Use for model-family comparison and independent-expert question design."
  "Model relevance is not same-object evidence."

fragmentationMovementReceipt : SnowballIdentifierReceipt
fragmentationMovementReceipt = snowball-identifier-receipt
  "Habitat fragmentation affects movement and space use of a specialist folivore, the koala"
  "peer-reviewed koala movement study"
  "2020"
  peerReviewedMechanism
  verified "10.1111/acv.12596"
  verified "Q913302"
  verified "577.27"
  "peer-reviewed mechanism/background source"
  "Supports the mechanism that reduced functional connectivity changes koala movement/space use and can increase movement costs across fragmented landscapes."
  "Independent study context, not Woogaroo-specific. Q913302 is the habitat-fragmentation concept QID, not the article identity."
  "Ask the current expert which measured connectivity quantities would distinguish redundant habitat from a bottleneck in Woogaroo."
  "Concept QID and mechanism paper do not prove local magnitude or statutory significance."

urbanMovementReceipt : SnowballIdentifierReceipt
urbanMovementReceipt = snowball-identifier-receipt
  "Patterns of activity and travel by koalas in a disturbed urban landscape in Queensland"
  "Philippa Kirsten Tacla; Benjamin James Barth; Sean Ian FitzGibbon; Amber Kristen Gillett; William Anthony Ellis"
  "2025"
  peerReviewedMechanism
  verified "10.1071/AM24044"
  unresolved "publication QID not safely resolved in this audit"
  verified "599.25"
  "peer-reviewed Queensland urban-koala study"
  "Supports current Queensland evidence that koalas move through disturbed urban landscapes and that movement ecology must be measured rather than inferred from static occupancy alone."
  "Independent scientific carrier, but not same-population evidence for Ipswich/Springfield."
  "Use to design current movement/connectivity expert questions, not to substitute for local telemetry/population evidence."
  "Queensland-wide relevance does not establish the Woogaroo population unit."

vehicleStrikeReceipt : SnowballIdentifierReceipt
vehicleStrikeReceipt = snowball-identifier-receipt
  "Koalas in space and time: Lessons from 20 years of vehicle-strike trends and hot spots in South East Queensland"
  "C. E. Dexter and coauthors"
  "2024"
  peerReviewedMechanism
  verified "10.1111/aec.13465"
  unresolved "publication QID not safely resolved in this audit"
  verified "599.25"
  "peer-reviewed SEQ threat-history source"
  "Supports the proposition that road-strike hot spots change with development/traffic pressures and may reflect changing local koala persistence."
  "Independent regional evidence; it does not prove road mortality at the Springview parcel."
  "Join local roads/development chronology to current expert assessment only if that threat pathway is material."
  "Regional threat mechanism does not equal local detrimental-effect proof."

incidentalDensityReceipt : SnowballIdentifierReceipt
incidentalDensityReceipt = snowball-identifier-receipt
  "Estimating koala density from incidental koala sightings in South-East Queensland, Australia (1997–2013), using a self-exciting spatio-temporal point process model"
  "Ravi Bandara Dissanayake; Emanuele Giorgi; Mark Stevenson; Rachel Allavena and coauthors"
  "2021"
  peerReviewedMechanism
  verified "10.1002/ece3.8082"
  unresolved "publication QID not safely resolved in this audit"
  verified "599.25"
  "peer-reviewed observation-modelling source"
  "Supports a method lineage for converting incidental sightings into population-density inference with explicit statistical assumptions."
  "Independent methodology; does not turn iNaturalist/FrogID/koala sightings into a local population estimate without a fitted model."
  "Potential future bridge from occurrence corpus to an independently estimated regional/local population object."
  "Observation density is not population viability or statutory essentiality."

------------------------------------------------------------------------
-- Consumer routing: what these sources can and cannot pay.
------------------------------------------------------------------------

data LegalAtom : Set where
  threatenedWildlifeStatusAtom
  threateningProcessMechanismAtom
  landscapeConnectivityMechanismAtom
  localPopulationContextAtom
  sameProjectExposureAtom
  likelySignificantDetrimentalEffectAtom
  viablePopulationIdentityAtom
  statutoryEssentialityAtom : LegalAtom

record SourceToAtomRoute : Set where
  constructor source-to-atom-route
  field
    sourceName : String
    atom : LegalAtom
    admissibleBackground : Bool
    consumerAdequateAlone : Bool
    routeNote : String

open SourceToAtomRoute public

ipswichToPopulationContext : SourceToAtomRoute
ipswichToPopulationContext = source-to-atom-route
  "Ipswich Koala Conservation and Habitat Management Plan"
  localPopulationContextAtom
  true false
  "Admissible independent regional context that Ipswich koalas are regionally important/genetically distinctive; does not alone identify the exact viable population relevant to s 13."

mcalpineToConnectivity : SourceToAtomRoute
mcalpineToConnectivity = source-to-atom-route
  "McAlpine/Rhodes landscape studies"
  landscapeConnectivityMechanismAtom
  true false
  "Admissible mechanism evidence that habitat amount/configuration and roads affect koala occurrence in fragmented SEQ landscapes; requires same-object current expert application."

movementToThreateningProcess : SourceToAtomRoute
movementToThreateningProcess = source-to-atom-route
  "fragmentation/movement literature"
  threateningProcessMechanismAtom
  true false
  "Admissible mechanism evidence for how fragmentation can affect movement and exposure to threats; does not establish the statutory conclusion for Woogaroo."

nonePaysFinalS102 : SourceToAtomRoute
nonePaysFinalS102 = source-to-atom-route
  "snowballed background literature"
  likelySignificantDetrimentalEffectAtom
  true false
  "The final s 102 bridge still requires a current same-object ecological opinion/application to the approved Woogaroo process."

nonePaysFinalS13 : SourceToAtomRoute
nonePaysFinalS13 = source-to-atom-route
  "snowballed background + Ipswich context"
  statutoryEssentialityAtom
  true false
  "The final s 13 bridge still requires an independently identified viable population/community and an essentiality counterfactual for this habitat."

------------------------------------------------------------------------
-- Reuse live consumer states; this file adds source/identifier structure only.
------------------------------------------------------------------------

s102State : S102.S102CaseState
s102State = S102.currentS102CaseState

s13State : S13.S13StressTest
s13State = S13.currentS13StressTest

------------------------------------------------------------------------
-- Snowball boundaries.
------------------------------------------------------------------------

data DOIEqualsTruth : Set where
data QIDEqualsSourceAuthority : Set where
data DeweyEqualsLegalRelevance : Set where
data MultiplePapersEqualsIndependentReplication : Set where
data RegionalPopulationContextEqualsLocalPopulationIdentity : Set where
data MechanismEvidenceEqualsSameProjectCausation : Set where

doiDoesNotCreateTruth : DOIEqualsTruth → ⊥
doiDoesNotCreateTruth ()

qidDoesNotCreateAuthority : QIDEqualsSourceAuthority → ⊥
qidDoesNotCreateAuthority ()

deweyDoesNotCreateLegalRelevance : DeweyEqualsLegalRelevance → ⊥
deweyDoesNotCreateLegalRelevance ()

paperCountDoesNotCreateReplication : MultiplePapersEqualsIndependentReplication → ⊥
paperCountDoesNotCreateReplication ()

regionalContextDoesNotFixPopulationIdentity : RegionalPopulationContextEqualsLocalPopulationIdentity → ⊥
regionalContextDoesNotFixPopulationIdentity ()

mechanismDoesNotCreateSameProjectCausation : MechanismEvidenceEqualsSameProjectCausation → ⊥
mechanismDoesNotCreateSameProjectCausation ()
