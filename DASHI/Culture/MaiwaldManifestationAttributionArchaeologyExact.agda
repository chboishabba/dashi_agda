module DASHI.Culture.MaiwaldManifestationAttributionArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MAIWALD MANIFESTATION-ATTRIBUTION ARCHAEOLOGY
--
-- Thin archaeology/navigation owner.  The scientific/project owner remains
-- DASHI.Culture.MaiwaldActionSpectroscopyProjectSuccessionExact.  This file
-- names the manifestation disagreement so later consumers do not normalize it
-- away or infer custody from a metadata mapping.
------------------------------------------------------------------------

data AttributionCarrierKind : Set where
  authorManuscript publisherSupportingInformation publisherRenderedPage
  bibliographicIndex conferenceProgramme : AttributionCarrierKind

record ManifestationAttributionCarrier : Set where
  constructor manifestation-attribution-carrier
  field
    kind : AttributionCarrierKind
    objectTitle : String
    stableIdentifier : String
    sourceLink : String
    sourceClass : String
    frankMaiwaldMapping : String
    explicitNumberedMapping : Bool
    primaryObjectCarrier : Bool

open ManifestationAttributionCarrier public

chemRxivCarrier : ManifestationAttributionCarrier
chemRxivCarrier = manifestation-attribution-carrier
  authorManuscript
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "ChemRxiv DOI 10.26434/chemrxiv-2024-2tvc6"
  "https://chemrxiv.org/doi/10.26434/chemrxiv-2024-2tvc6"
  "primary author manuscript manifestation"
  "Frank Maiwald affiliation 2 = Jet Propulsion Laboratory, California Institute of Technology"
  true true

acsSupportingInformationCarrier : ManifestationAttributionCarrier
acsSupportingInformationCarrier = manifestation-attribution-carrier
  publisherSupportingInformation
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects — Supporting Information"
  "parent DOI 10.1021/acs.jpca.4c03552; ACS SI jp4c03552_si_001"
  "https://pubs.acs.org/doi/suppl/10.1021/acs.jpca.4c03552/suppl_file/jp4c03552_si_001.pdf"
  "primary publisher supporting-information manifestation"
  "Frank Maiwald affiliation 2 = NASA Jet Propulsion Laboratory, California Institute of Technology"
  true true

isms2024Carrier : ManifestationAttributionCarrier
isms2024Carrier = manifestation-attribution-carrier
  conferenceProgramme
  "Cryogenic Ion Vibrational Spectroscopy of Deprotonated Valine and Deprotonated Aminovaleric Acid"
  "ISMS P7658 / RL06; 2024-06-20"
  "https://isms.illinois.edu/2024/schedule/schedule_session.php?sID=1564"
  "primary conference programme/abstract"
  "Frank Maiwald = Jet Propulsion Laboratory, California Institute of Technology"
  false true

acsRenderedCarrier : ManifestationAttributionCarrier
acsRenderedCarrier = manifestation-attribution-carrier
  publisherRenderedPage
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "DOI 10.1021/acs.jpca.4c03552"
  "https://pubs.acs.org/doi/10.1021/acs.jpca.4c03552"
  "publisher rendered author metadata"
  "current rendered page maps Frank Maiwald to JILA and Department of Chemistry, University of Colorado Boulder"
  false true

pubmedCarrier : ManifestationAttributionCarrier
pubmedCarrier = manifestation-attribution-carrier
  bibliographicIndex
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "PMID 39150465; DOI 10.1021/acs.jpca.4c03552"
  "https://pubmed.ncbi.nlm.nih.gov/39150465/"
  "bibliographic index derived from publication metadata"
  "current PubMed mapping assigns Frank Maiwald affiliation 1 = JILA and Department of Chemistry, University of Colorado Boulder"
  false false

------------------------------------------------------------------------
-- Named conflict and bounded resolution state.
------------------------------------------------------------------------

record ManifestationAttributionConflict : Set where
  constructor manifestation-attribution-conflict
  field
    conflictName : String
    publicationDOI : String
    author : String
    explicitPrimaryMappingsAgree : Bool
    explicitPrimaryMapping : String
    renderedAndIndexMappingsAgreeWithExplicitPrimary : Bool
    metadataConflictRetained : Bool
    sourceTextSupportsJPLAffiliationForThisObject : Bool
    canonicalMetadataHarmonisationPaid : Bool
    affiliationConflictDeterminesApparatusCustody : Bool
    affiliationConflictDeterminesRawDataCustody : Bool
    affiliationConflictDeterminesEmploymentAtEventTime : Bool
    acquisitionTarget : String

open ManifestationAttributionConflict public

protonatedValineMaiwaldConflict : ManifestationAttributionConflict
protonatedValineMaiwaldConflict = manifestation-attribution-conflict
  "Maiwald protonated-valine manifestation affiliation conflict"
  "10.1021/acs.jpca.4c03552"
  "Frank W. Maiwald"
  true
  "ChemRxiv numbered author block + ACS Supporting Information explicitly assign Maiwald to JPL/Caltech; ISMS independently gives JPL/Caltech"
  false
  true
  true
  false
  false false false
  "publisher/Crossref production metadata or correction history explaining why ACS rendered/PubMed mapping assigns Maiwald to JILA while the manuscript and ACS SI assign him to JPL"

------------------------------------------------------------------------
-- Same-name DOI/dataset false-positive control.
--
-- A generic dataset search returns a 2023 Mendeley Data object entitled
-- `Transcriptome atlas of the honeybee across development stages`, DOI
-- 10.17632/7pyv3ccrzt.1, whose contributor list contains a Frank Maiwald.
-- Its domain/coauthors are insect physiology/toxicology and do not match the
-- independently paid JPL Frank W. Maiwald identity.  The object is therefore a
-- useful negative control for automated DOI/QID snowballing: same display name,
-- year proximity and a real DOI cannot manufacture person identity.
------------------------------------------------------------------------

record SameNameDatasetCollision : Set where
  constructor same-name-dataset-collision
  field
    candidateName : String
    candidateObject : String
    candidateDOI : String
    candidateSourceLink : String
    candidateDomain : String
    targetIdentity : String
    targetIdentityCarrier : String
    exactPersonIdentityPaid : Bool
    mayAttachCandidateDOIToTarget : Bool
    mayTreatDatasetAsJPLActionSpectroscopyData : Bool
    usefulAsNegativeControl : Bool

open SameNameDatasetCollision public

honeybeeFrankMaiwaldCollision : SameNameDatasetCollision
honeybeeFrankMaiwaldCollision = same-name-dataset-collision
  "Frank Maiwald"
  "Transcriptome atlas of the honeybee across development stages"
  "10.17632/7pyv3ccrzt.1"
  "https://data.mendeley.com/datasets/7pyv3ccrzt"
  "insect physiology / insect toxicology / honeybee transcriptomics"
  "Frank W. Maiwald, NASA Jet Propulsion Laboratory / Caltech"
  "JPL SURP SP23012p; JPL Principal designation; DOI 10.1021/acs.analchem.4c01023 and other JPL publication carriers"
  false
  false
  false
  true

------------------------------------------------------------------------
-- Snowball coordinates: identity/search only, never authority.
------------------------------------------------------------------------

record ManifestationAttributionCoordinate : Set where
  constructor manifestation-attribution-coordinate
  field
    doi : String
    qid : String
    qidMeaning : String
    deweyTraversal : String
    qidVerified : Bool
    personQidResolved : Bool
    deweyCreatesAuthority : Bool
    qidCreatesCustody : Bool

open ManifestationAttributionCoordinate public

maiwaldProtonatedCoordinate : ManifestationAttributionCoordinate
maiwaldProtonatedCoordinate = manifestation-attribution-coordinate
  "10.1021/acs.jpca.4c03552"
  "Q189325"
  "Jet Propulsion Laboratory institution coordinate only; Frank Maiwald person QID unresolved"
  "540 Chemistry"
  true false false false

------------------------------------------------------------------------
-- Archaeology firewalls.
------------------------------------------------------------------------

record ManifestationAttributionBoundary : Set where
  constructor manifestation-attribution-boundary
  field
    sameDoiMeansSameMetadataAcrossManifestations : Bool
    indexMappingOverridesExplicitSourceText : Bool
    explicitSourceTextDeletesConflictingIndexHistory : Bool
    affiliationImpliesApparatusOwnership : Bool
    affiliationImpliesDataCustody : Bool
    sameDisplayNamePlusDoiPaysPersonIdentity : Bool
    crossDomainDatasetMayBeInheritedByName : Bool
    conflictShouldRemainNamed : Bool

open ManifestationAttributionBoundary public

canonicalManifestationAttributionBoundary : ManifestationAttributionBoundary
canonicalManifestationAttributionBoundary = manifestation-attribution-boundary
  false false false false false false false true
