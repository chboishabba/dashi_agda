module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCitationNeighbourhoodExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as LiAttr

------------------------------------------------------------------------
-- ATTRIBUTION-SAFE AdK CITATION / RELATED-SOURCE NEIGHBOURHOOD
--
-- This atlas broadens acquisition beyond Li-Liu-Ji 2015 while preserving the
-- repository's attribution firewall.  A paper may be a predecessor, a later
-- related study, or a verified citer of Li-Liu-Ji; none of those relations
-- transfers numeric cells, observable identity, mechanism, or authority.
--
-- DOI/PMID/PMCID/OpenAlex/QID are retained as identity coordinates only.
-- Unresolved article QIDs and absent PMCID/OpenAlex coordinates stay explicit.
------------------------------------------------------------------------

data SourceRelation : Set where
  anchorArticle : SourceRelation
  predecessorRelatedStudy : SourceRelation
  laterRelatedStudy : SourceRelation
  verifiedCitesLi2015 : SourceRelation
  indexedCitationToLi2015 : SourceRelation

data AcquisitionRole : Set where
  apoDynamicsRole : AcquisitionRole
  freeEnergyRole : AcquisitionRole
  pathwayTimescaleRole : AcquisitionRole
  replicaExchangeRole : AcquisitionRole
  substrateBindingRole : AcquisitionRole

record RelatedAdKSource : Set where
  constructor related-adk-source
  field
    source : Attribution.AttributedSource
    relation : SourceRelation
    role : AcquisitionRole
    pmid : Identity.ExternalIdentityDemand
    pmcid : Identity.ExternalIdentityDemand
    openAlex : Identity.ExternalIdentityDemand
    articleQid : Identity.ExternalIdentityDemand
    relationLocator : String
    acquisitionReading : String
open RelatedAdKSource public

mkUnresolvedId : String → String → Identity.ExternalIdentityDemand
mkUnresolvedId label reason =
  Identity.mkOptionalIdentityDemand
    "AdK citation-neighbourhood acquisition"
    label
    label
    Identity.officialIdentifier
    (Identity.unresolved reason)

mkVerifiedId : String → String → String → Identity.ExternalIdentityDemand
mkVerifiedId label authority value =
  Identity.mkOptionalIdentityDemand
    "AdK citation-neighbourhood acquisition"
    label
    label
    Identity.officialIdentifier
    (Identity.verified authority value)

liLiuJi2015 : RelatedAdKSource
liLiuJi2015 = related-adk-source
  LiAttr.liLiuJiSource
  anchorArticle
  pathwayTimescaleRole
  LiAttr.articlePMID
  LiAttr.articlePMCID
  LiAttr.articleOpenAlex
  LiAttr.articleQID
  "Li-Liu-Ji 2015 DOI 10.1016/j.bpj.2015.06.059"
  "anchor article; existing source-paid AdK CV, landscape, pathway and Kramers-methodology roles are retained only in their existing owners"

songZhu2013Source : Attribution.AttributedSource
songZhu2013Source = Attribution.mkDOISource
  "Hyun Deok Song and Fangqiang Zhu"
  "Conformational Dynamics of a Ligand-Free Adenylate Kinase"
  "PLoS ONE"
  "2013"
  "10.1371/journal.pone.0068023"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC3702565/"
  Attribution.academicArticleSource
  "pays its own ligand-free AdK molecular-dynamics observations; it does not inherit Li-Liu-Ji state labels or calibration cells"
  Attribution.publicAttribution

songZhu2013 : RelatedAdKSource
songZhu2013 = related-adk-source
  songZhu2013Source predecessorRelatedStudy apoDynamicsRole
  (mkVerifiedId "Song-Zhu 2013 PMID" "PubMed" "23861846")
  (mkVerifiedId "Song-Zhu 2013 PMCID" "PubMed Central" "PMC3702565")
  (mkUnresolvedId "Song-Zhu 2013 OpenAlex work" "not verified in this acquisition pass")
  (mkUnresolvedId "Song-Zhu 2013 article QID" "article-level QID unresolved")
  "PubMed/PMC article identity; predecessor cited in later AdK literature neighbourhood"
  "free MD simulations from open/closed starting conformations; alternate observables/methods require same-definition gates before any cross-paper numeric use"

formoso2015Source : Attribution.AttributedSource
formoso2015Source = Attribution.mkDOISource
  "Elena Formoso, Vittorio Limongelli and Michele Parrinello"
  "Energetics and Structural Characterization of the large-scale Functional Motion of Adenylate Kinase"
  "Scientific Reports"
  "2015"
  "10.1038/srep08425"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC4325324/"
  Attribution.academicArticleSource
  "pays its own metadynamics thermodynamic and structural observations only"
  Attribution.publicAttribution

formoso2015 : RelatedAdKSource
formoso2015 = related-adk-source
  formoso2015Source predecessorRelatedStudy freeEnergyRole
  (mkVerifiedId "Formoso-Limongelli-Parrinello 2015 PMID" "PubMed" "25672826")
  (mkVerifiedId "Formoso-Limongelli-Parrinello 2015 PMCID" "PubMed Central" "PMC4325324")
  (mkUnresolvedId "Formoso-Limongelli-Parrinello OpenAlex work" "not verified in this acquisition pass")
  (mkUnresolvedId "Formoso-Limongelli-Parrinello article QID" "article-level QID unresolved")
  "PubMed/PMC article identity; neighbouring 2015 metadynamics study"
  "independent free-energy/structural study; its coordinate system cannot be identified with Li-Liu-Ji CVs by topic similarity alone"

zhengCui2018Source : Attribution.AttributedSource
zhengCui2018Source = Attribution.mkDOISource
  "Yuqing Zheng and Qiang Cui"
  "Multiple Pathways and Time Scales for Conformational Transitions in apo-Adenylate Kinase"
  "Journal of Chemical Theory and Computation"
  "2018"
  "10.1021/acs.jctc.7b01064"
  "https://pubmed.ncbi.nlm.nih.gov/29378407/"
  Attribution.academicArticleSource
  "pays its own approximately 50 microsecond atomistic/Markov-state apo-AdK pathway and timescale observations only"
  Attribution.publicAttribution

zhengCui2018 : RelatedAdKSource
zhengCui2018 = related-adk-source
  zhengCui2018Source indexedCitationToLi2015 pathwayTimescaleRole
  (mkVerifiedId "Zheng-Cui 2018 PMID" "PubMed" "29378407")
  (mkUnresolvedId "Zheng-Cui 2018 PMCID" "no PMCID verified in inspected PubMed record")
  (mkUnresolvedId "Zheng-Cui 2018 OpenAlex work" "not verified in this acquisition pass")
  (mkUnresolvedId "Zheng-Cui 2018 article QID" "article-level QID unresolved")
  "bibliographic reference index for the Zheng-Cui article lists Li-Liu-Ji 2015; PubMed/ACS pay the Zheng-Cui article identity and abstract claims"
  "later apo-AdK pathway/timescale study; citation relation does not create same-observable or same-state identity"

wang2020Source : Attribution.AttributedSource
wang2020Source = Attribution.mkDOISource
  "Jinan Wang et al."
  "Exploring Conformational Change of Adenylate Kinase by Replica Exchange Molecular Dynamic Simulation"
  "Biophysical Journal"
  "2020"
  "10.1016/j.bpj.2020.01.001"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC7063423/"
  Attribution.academicArticleSource
  "pays its own vsREMD/conventional-REMD comparison and associated free-energy profile observations only"
  Attribution.publicAttribution

wang2020 : RelatedAdKSource
wang2020 = related-adk-source
  wang2020Source laterRelatedStudy replicaExchangeRole
  (mkVerifiedId "Wang et al. 2020 PMID" "PubMed" "31995738")
  (mkVerifiedId "Wang et al. 2020 PMCID" "PubMed Central" "PMC7063423")
  (mkVerifiedId "Wang et al. 2020 OpenAlex" "OpenAlex" "W2998867693")
  (mkUnresolvedId "Wang et al. 2020 article QID" "article-level QID unresolved")
  "PubMed/PMC/OpenAlex identity; later AdK enhanced-sampling study in the same literature neighbourhood"
  "30-replica vsREMD versus 80-replica conventional REMD at similar ~0.2 acceptance is method evidence, not Li-Liu-Ji calibration"

lu2022Source : Attribution.AttributedSource
lu2022Source = Attribution.mkDOISource
  "Jiajun Lu, David Scheerer, Gilad Haran, Wenfei Li and Wei Wang"
  "Role of Repeated Conformational Transitions in Substrate Binding of Adenylate Kinase"
  "The Journal of Physical Chemistry B"
  "2022"
  "10.1021/acs.jpcb.2c05497"
  "https://pmc.ncbi.nlm.nih.gov/articles/PMC9589722/"
  Attribution.academicArticleSource
  "pays its own substrate-binding simulation/free-energy mechanism observations and its bibliography relation to prior AdK literature"
  Attribution.publicAttribution

lu2022 : RelatedAdKSource
lu2022 = related-adk-source
  lu2022Source verifiedCitesLi2015 substrateBindingRole
  (mkVerifiedId "Lu et al. 2022 PMID" "PubMed" "36222098")
  (mkVerifiedId "Lu et al. 2022 PMCID" "PubMed Central" "PMC9589722")
  (mkVerifiedId "Lu et al. 2022 OpenAlex" "OpenAlex" "W4304688442")
  (mkUnresolvedId "Lu et al. 2022 article QID" "article-level QID unresolved")
  "ACS/PMC reference list includes Li-Liu-Ji 2015 DOI 10.1016/j.bpj.2015.06.059"
  "later citing study on repeated conformational transitions during substrate binding; it adds an independent mechanistic/model context rather than upgrading Li-Liu-Ji cells"

songReceipt : Snowball.SourceRoleSnowballReceipt songZhu2013Source
songReceipt = Snowball.canonicalSourceRoleSnowballReceipt songZhu2013Source
formosoReceipt : Snowball.SourceRoleSnowballReceipt formoso2015Source
formosoReceipt = Snowball.canonicalSourceRoleSnowballReceipt formoso2015Source
zhengReceipt : Snowball.SourceRoleSnowballReceipt zhengCui2018Source
zhengReceipt = Snowball.canonicalSourceRoleSnowballReceipt zhengCui2018Source
wangReceipt : Snowball.SourceRoleSnowballReceipt wang2020Source
wangReceipt = Snowball.canonicalSourceRoleSnowballReceipt wang2020Source
luReceipt : Snowball.SourceRoleSnowballReceipt lu2022Source
luReceipt = Snowball.canonicalSourceRoleSnowballReceipt lu2022Source

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data CitationImportsLiNumericCells : Set where
data RelatedObservableMeansSameObservable : Set where
data LaterMechanismOverridesEarlierSource : Set where
data QidCreatesCrossPaperIdentity : Set where

citationDoesNotImportLiNumericCells : CitationImportsLiNumericCells → ⊥
citationDoesNotImportLiNumericCells ()
relatedDoesNotMeanSameObservable : RelatedObservableMeansSameObservable → ⊥
relatedDoesNotMeanSameObservable ()
laterDoesNotOverrideEarlierSource : LaterMechanismOverridesEarlierSource → ⊥
laterDoesNotOverrideEarlierSource ()
qidDoesNotCreateCrossPaperIdentity : QidCreatesCrossPaperIdentity → ⊥
qidDoesNotCreateCrossPaperIdentity ()

record AdKCitationNeighbourhoodBoundary : Set where
  constructor adk-citation-neighbourhood-boundary
  field
    liLiuJiAnchorRetained : Bool
    songZhu2013Retained : Bool
    formoso2015Retained : Bool
    zhengCui2018Retained : Bool
    wang2020Retained : Bool
    lu2022Retained : Bool
    citationImportsLiNumericCells : Bool
    relatedObservableMeansSameObservable : Bool
    laterMechanismOverridesEarlierSource : Bool
    qidCreatesCrossPaperIdentity : Bool
    unresolvedArticleQidsRemainExplicit : Bool
    sourceLocalRolesRetained : Bool
open AdKCitationNeighbourhoodBoundary public

canonicalAdKCitationNeighbourhoodBoundary : AdKCitationNeighbourhoodBoundary
canonicalAdKCitationNeighbourhoodBoundary = adk-citation-neighbourhood-boundary
  true true true true true true
  false false false false
  true true
