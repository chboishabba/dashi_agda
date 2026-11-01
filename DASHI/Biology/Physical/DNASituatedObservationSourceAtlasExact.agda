module DASHI.Biology.Physical.DNASituatedObservationSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- DNA SITUATED-OBSERVATION SOURCE ATLAS
--
-- This source atlas separates publication identity from coordinate convention
-- and from sequence-dependent structural observations.  The repository's exact
-- finite UV base chart remains DASHI algebra; these literature sources do not
-- acquire authorship of that chart or of any DASHI FactorsThrough theorem.
------------------------------------------------------------------------

data DNASourceRole : Set where
  doubleHelixHistoricalRole
  standardBasePairFrameRole
  nearestNeighbourGeometryRole
  tetranucleotideContextGeometryRole : DNASourceRole

record DNASourceStudy : Set where
  constructor dna-source-study
  field
    label : String
    source : Attribution.AttributedSource
    role : DNASourceRole
    pmid : String
    pmcid : String
    articleQid : Identity.ExternalIdentityDemand
    observationDefinition : String
    sourceBoundedFinding : String
    nonPromotion : String
open DNASourceStudy public

mkArticleQidDemand : String → String → Identity.ExternalIdentityDemand
mkArticleQidDemand label title =
  Identity.mkOptionalIdentityDemand
    "DNA situated-observation source atlas"
    label
    title
    Identity.wikidataQid
    (Identity.unresolved "article-level Wikidata QID not independently verified")

watsonCrick1953 : DNASourceStudy
watsonCrick1953 = dna-source-study
  "Watson and Crick 1953 DNA structural paper"
  (Attribution.mkDOISource
    "Watson and Crick"
    "Molecular structure of nucleic acids; a structure for deoxyribose nucleic acid"
    "Nature"
    "1953"
    "10.1038/171737a0"
    "https://pubmed.ncbi.nlm.nih.gov/13054692/"
    Attribution.academicArticleSource
    "pays the historical source role for the double-helical DNA structure described in the paper; does not pay later DASHI coordinate systems"
    Attribution.publicAttribution)
  doubleHelixHistoricalRole
  "13054692"
  "PMCID not applicable/unresolved"
  (mkArticleQidDemand "Watson-Crick 1953 article QID" "Molecular structure of nucleic acids; a structure for deoxyribose nucleic acid")
  "historical molecular-structure description"
  "source role limited to the published 1953 structural proposal and its own claims"
  "does not create the repository UV chart, modern base-pair-frame convention, or universal solution-state geometry"

olson2001 : DNASourceStudy
olson2001 = dna-source-study
  "Olson et al. 2001 standard base-pair reference frame"
  (Attribution.mkDOISource
    "Olson, Bansal, Burley, Dickerson, Gerstein, Harvey, Heinemann, Lu, Neidle, Shakked, Sklenar, Suzuki, Tung, Westhof, Wolberger and Berman"
    "A standard reference frame for the description of nucleic acid base-pair geometry"
    "Journal of Molecular Biology"
    "2001"
    "10.1006/jmbi.2001.4987"
    "https://pubmed.ncbi.nlm.nih.gov/11601858/"
    Attribution.academicArticleSource
    "pays the standard-reference-frame source role for nucleic-acid base-pair geometry descriptions"
    Attribution.publicAttribution)
  standardBasePairFrameRole
  "11601858"
  "PMCID unresolved in inspected source"
  (mkArticleQidDemand "Olson 2001 article QID" "A standard reference frame for the description of nucleic acid base-pair geometry")
  "source-defined base-pair/base-pair-step reference-frame convention"
  "paper provides a standard geometry-description framework; coordinate meaning depends on this retained convention"
  "same parameter name under another convention is not automatically the same measurement object"

lavery2010 : DNASourceStudy
lavery2010 = dna-source-study
  "Lavery et al. nearest-neighbour B-DNA geometry study"
  (Attribution.mkDOISource
    "Lavery et al."
    "A systematic molecular dynamics study of nearest-neighbor effects on base pair and base pair step conformations and fluctuations in B-DNA"
    "Nucleic Acids Research"
    "2010"
    "10.1093/nar/gkp834"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC2800215/"
    Attribution.academicArticleSource
    "pays the study's molecular-dynamics observations of sequence-dependent base-pair and step conformations/fluctuations"
    Attribution.publicAttribution)
  nearestNeighbourGeometryRole
  "19850719"
  "PMC2800215"
  (mkArticleQidDemand "Lavery 2010 article QID" "A systematic molecular dynamics study of nearest-neighbor effects on base pair and base pair step conformations and fluctuations in B-DNA")
  "MD-derived base-pair/base-pair-step conformational and fluctuation observables"
  "nearest-neighbour sequence context affects the observed geometry/fluctuation distributions in the study"
  "does not make one ideal B-DNA step a universal sequence-independent geometry"

pasi2014 : DNASourceStudy
pasi2014 = dna-source-study
  "Pasi et al. microsecond tetranucleotide B-DNA study"
  (Attribution.mkDOISource
    "Pasi et al."
    "μABC: a systematic microsecond molecular dynamics study of tetranucleotide sequence effects in B-DNA"
    "Nucleic Acids Research"
    "2014"
    "10.1093/nar/gku855"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4231739/"
    Attribution.academicArticleSource
    "pays the study's tetranucleotide-context effects on average helical parameters, fluctuations and conformational substates"
    Attribution.publicAttribution)
  tetranucleotideContextGeometryRole
  "25260586"
  "PMC4231739"
  (mkArticleQidDemand "Pasi 2014 article QID" "μABC: a systematic microsecond molecular dynamics study of tetranucleotide sequence effects in B-DNA")
  "microsecond MD over oligomers containing all 136 distinct tetranucleotide sequences"
  "source reports that helical parameters and fluctuations depend on the step and its flanking base pairs, with some sequences sampling distinct substates"
  "does not promote simulation conformational distributions to every experimental environment or complete DNA state"

olsonReceipt : Snowball.SourceRoleSnowballReceipt (source olson2001)
olsonReceipt = Snowball.canonicalSourceRoleSnowballReceipt (source olson2001)

pasiReceipt : Snowball.SourceRoleSnowballReceipt (source pasi2014)
pasiReceipt = Snowball.canonicalSourceRoleSnowballReceipt (source pasi2014)

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data CitationCreatesGeometryTruth : Set where
data SameHelicalParameterNameCreatesSameObservable : Set where
data SameDinucleotideCreatesContextIndependentGeometry : Set where
data ExactUVBaseChartCreatesCompleteDNAState : Set where

citationDoesNotCreateGeometryTruth : CitationCreatesGeometryTruth → ⊥
citationDoesNotCreateGeometryTruth ()

sameNameDoesNotCreateSameObservable : SameHelicalParameterNameCreatesSameObservable → ⊥
sameNameDoesNotCreateSameObservable ()

sameDinucleotideDoesNotCreateContextIndependentGeometry :
  SameDinucleotideCreatesContextIndependentGeometry → ⊥
sameDinucleotideDoesNotCreateContextIndependentGeometry ()

exactUVChartDoesNotCreateCompleteDNAState : ExactUVBaseChartCreatesCompleteDNAState → ⊥
exactUVChartDoesNotCreateCompleteDNAState ()

record DNASituatedObservationSourceAtlasBoundary : Set where
  constructor dna-situated-observation-source-atlas-boundary
  field
    historicalHelixSourceRetained : Bool
    standardFrameSourcePaid : Bool
    sequenceContextSourcePaid : Bool
    tetranucleotideContextSourcePaid : Bool
    articleQidsMayRemainUnresolved : Bool
    citationCreatesGeometryTruth : Bool
    sameParameterNameCreatesSameObservable : Bool
    sameDinucleotideCreatesContextIndependentGeometry : Bool
    exactUVChartCreatesCompleteDNAState : Bool
open DNASituatedObservationSourceAtlasBoundary public

canonicalDNASituatedObservationSourceAtlasBoundary : DNASituatedObservationSourceAtlasBoundary
canonicalDNASituatedObservationSourceAtlasBoundary =
  dna-situated-observation-source-atlas-boundary
    true true true true true
    false false false false
