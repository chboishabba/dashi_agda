module DASHI.Biology.Protein.AlliumThiolSourceAttributionEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ALLIUM / ALLICIN PROTEIN-THIOL SOURCE ATTRIBUTION ENVELOPE
--
-- Publication/object identities retain provenance only.  They do not create
-- the protein-site accessibility proposition, a modification outcome, a
-- functional mechanism, or a DASHI query/factorisation theorem.
------------------------------------------------------------------------

rabinkov1998 : Attribution.AttributedSource
rabinkov1998 =
  Attribution.mkDOISource
    "Rabinkov, Miron, Konstantinovski, Wilchek, Mirelman and Weiner"
    "The mode of action of allicin: trapping of radicals and interaction with thiol containing proteins"
    "Biochimica et Biophysica Acta"
    "1998"
    "10.1016/S0304-4165(97)00104-9"
    "https://pubmed.ncbi.nlm.nih.gov/9528659/"
    Attribution.academicArticleSource
    "pays source-bounded allicin/thiol-protein chemistry and enzyme-thiol interaction observations; does not pay a universal cysteine-modification law"
    Attribution.publicAttribution

borlinghaus2014 : Attribution.AttributedSource
borlinghaus2014 =
  Attribution.mkDOISource
    "Borlinghaus, Albrecht, Gruhlke, Nwachukwu and Slusarenko"
    "Allicin: chemistry and biological properties"
    "Molecules"
    "2014"
    "10.3390/molecules190812591"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC6271412/"
    Attribution.academicArticleSource
    "review source for allicin chemistry and biological thiol reactivity; does not create target-specific modification authority"
    Attribution.publicAttribution

borlinghaus2021 : Attribution.AttributedSource
borlinghaus2021 =
  Attribution.mkDOISource
    "Borlinghaus, Foerster nee Reiter, Kappler, Antelmann, Noll, Gruhlke and Slusarenko"
    "Allicin, the Odor of Freshly Crushed Garlic: A Review of Recent Progress in Understanding Allicin's Effects on Cells"
    "Molecules"
    "2021"
    "10.3390/molecules26061505"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC8001868/"
    Attribution.academicArticleSource
    "review source explicitly describing S-thioallylation of accessible cysteine residues and low-molecular-weight thiols; does not pay a universal protein-mechanism theorem"
    Attribution.publicAttribution

rabinkovReceipt : Snowball.SourceRoleSnowballReceipt rabinkov1998
rabinkovReceipt = Snowball.canonicalSourceRoleSnowballReceipt rabinkov1998

borlinghaus2014Receipt : Snowball.SourceRoleSnowballReceipt borlinghaus2014
borlinghaus2014Receipt = Snowball.canonicalSourceRoleSnowballReceipt borlinghaus2014

borlinghaus2021Receipt : Snowball.SourceRoleSnowballReceipt borlinghaus2021
borlinghaus2021Receipt = Snowball.canonicalSourceRoleSnowballReceipt borlinghaus2021

------------------------------------------------------------------------
-- External identities.  Article QIDs remain unresolved unless independently
-- verified.  DOI/PMID/PMCID do not substitute for those QIDs.
------------------------------------------------------------------------

rabinkovDOI : Identity.ExternalIdentityDemand
rabinkovDOI = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Rabinkov 1998 DOI"
  "The mode of action of allicin"
  Identity.doi
  (Identity.verified "DOI/PubMed" "10.1016/S0304-4165(97)00104-9")

rabinkovPMID : Identity.ExternalIdentityDemand
rabinkovPMID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Rabinkov 1998 PMID"
  "The mode of action of allicin"
  Identity.officialIdentifier
  (Identity.verified "PubMed" "9528659")

rabinkovArticleQID : Identity.ExternalIdentityDemand
rabinkovArticleQID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Rabinkov 1998 article QID"
  "The mode of action of allicin"
  Identity.wikidataQid
  (Identity.unresolved "article-level QID not verified")

borlinghaus2014DOI : Identity.ExternalIdentityDemand
borlinghaus2014DOI = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2014 DOI"
  "Allicin: chemistry and biological properties"
  Identity.doi
  (Identity.verified "DOI/PubMed" "10.3390/molecules190812591")

borlinghaus2014PMID : Identity.ExternalIdentityDemand
borlinghaus2014PMID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2014 PMID"
  "Allicin: chemistry and biological properties"
  Identity.officialIdentifier
  (Identity.verified "PubMed" "25153873")

borlinghaus2014PMCID : Identity.ExternalIdentityDemand
borlinghaus2014PMCID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2014 PMCID"
  "Allicin: chemistry and biological properties"
  Identity.officialIdentifier
  (Identity.verified "PubMed Central" "PMC6271412")

borlinghaus2014ArticleQID : Identity.ExternalIdentityDemand
borlinghaus2014ArticleQID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2014 article QID"
  "Allicin: chemistry and biological properties"
  Identity.wikidataQid
  (Identity.unresolved "article-level QID not verified")

borlinghaus2021DOI : Identity.ExternalIdentityDemand
borlinghaus2021DOI = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2021 DOI"
  "Allicin, the Odor of Freshly Crushed Garlic"
  Identity.doi
  (Identity.verified "DOI/PubMed" "10.3390/molecules26061505")

borlinghaus2021PMID : Identity.ExternalIdentityDemand
borlinghaus2021PMID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2021 PMID"
  "Allicin, the Odor of Freshly Crushed Garlic"
  Identity.officialIdentifier
  (Identity.verified "PubMed" "33801955")

borlinghaus2021PMCID : Identity.ExternalIdentityDemand
borlinghaus2021PMCID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2021 PMCID"
  "Allicin, the Odor of Freshly Crushed Garlic"
  Identity.officialIdentifier
  (Identity.verified "PubMed Central" "PMC8001868")

borlinghaus2021ArticleQID : Identity.ExternalIdentityDemand
borlinghaus2021ArticleQID = Identity.mkOptionalIdentityDemand
  "Allium thiol source attribution"
  "Borlinghaus 2021 article QID"
  "Allicin, the Odor of Freshly Crushed Garlic"
  Identity.wikidataQid
  (Identity.unresolved "article-level QID not verified")

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DOIOrPMIDCreatesModification : Set where
data ReviewCitationCreatesUniversalTargetLaw : Set where
data UnresolvedQIDBlocksSourceUse : Set where

doiOrPmidDoesNotCreateModification : DOIOrPMIDCreatesModification → ⊥
doiOrPmidDoesNotCreateModification ()

reviewDoesNotCreateUniversalTargetLaw : ReviewCitationCreatesUniversalTargetLaw → ⊥
reviewDoesNotCreateUniversalTargetLaw ()

unresolvedQidDoesNotBlockSourceUse : UnresolvedQIDBlocksSourceUse → ⊥
unresolvedQidDoesNotBlockSourceUse ()

record AlliumThiolSourceAttributionBoundary : Set where
  constructor allium-thiol-source-attribution-boundary
  field
    attributedSourceCoreReused : Bool
    snowballSourceRoleRetained : Bool
    doiPmidPmcidRetained : Bool
    articleQidMayRemainUnresolved : Bool
    citationCreatesModificationAuthority : Bool
    reviewCreatesUniversalTargetLaw : Bool
open AlliumThiolSourceAttributionBoundary public

canonicalAlliumThiolSourceAttributionBoundary : AlliumThiolSourceAttributionBoundary
canonicalAlliumThiolSourceAttributionBoundary =
  allium-thiol-source-attribution-boundary
    true true true true false false
