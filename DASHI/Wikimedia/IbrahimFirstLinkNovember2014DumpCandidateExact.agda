module DASHI.Wikimedia.IbrahimFirstLinkNovember2014DumpCandidateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimFirstLinkHistoricalDiscriminatorParetoExact as Pareto

------------------------------------------------------------------------
-- NOVEMBER-2014 DUMP CANDIDATE
--
-- Independent contemporary dump-list evidence identifies an English Wikipedia
-- pages-articles snapshot dated 2014-11-06.  This is a candidate compatible
-- with the paper's month-level description, not evidence that Ibrahim's local
-- full_wiki_data was derived from this exact dump.
------------------------------------------------------------------------

record DumpCandidateReceipt : Set where
  constructor dump-candidate-receipt
  field
    dumpDate : String
    project : String
    filename : String
    reportedCompressedSize : String
    sourceRole : String
    sourceLink : String
    compatibleWithPaperMonth : Bool
    sameObjectWithIbrahimInputPaid : Bool
    checksumJoinedToIbrahimInput : Bool
open DumpCandidateReceipt public

november06Candidate : DumpCandidateReceipt
november06Candidate = dump-candidate-receipt
  "2014-11-06"
  "English Wikipedia"
  "enwiki-20141106-pages-articles-multistream.xml.bz2"
  "11.3 GB as reported in June-2015 Wikimedia XML-dumps mailing-list discussion"
  "independent historical dump-availability evidence; not Ibrahim production provenance"
  "https://lists.wikimedia.org/hyperkitty/list/xmldatadumps-l@lists.wikimedia.org/thread/UO4YJ2DYYZGVCKTMKVL7VNQTKDWZMHS4/"
  true false false

november06CandidateCorpus : Pareto.CandidateCorpus
november06CandidateCorpus = Pareto.candidate-corpus
  "English Wikipedia dump candidate 2014-11-06"
  "independently documented November-2014 enwiki pages-articles dump; candidate compatible with primary paper month but not joined to Ibrahim full_wiki_data"
  "http://dumps.wikimedia.org/enwiki/20141106/"
  false

candidateComparison : String
candidateComparison =
  "compare page/revision content and parser output for 20141008 versus 20141106 using primary-paper oracle edges; a differing edge can cheaply eliminate one candidate, while matching edges do not prove either whole corpus"

data NovemberCandidateMeansProductionDump : Set where
data SimilarArchiveSizeMeansSameObject : Set where
data MonthCompatibilityMeansIdentity : Set where

candidateDoesNotBecomeProductionDump : NovemberCandidateMeansProductionDump → ⊥
candidateDoesNotBecomeProductionDump ()

sizeDoesNotCreateSameObject : SimilarArchiveSizeMeansSameObject → ⊥
sizeDoesNotCreateSameObject ()

monthCompatibilityDoesNotCreateIdentity : MonthCompatibilityMeansIdentity → ⊥
monthCompatibilityDoesNotCreateIdentity ()

record NovemberCandidateBoundary : Set where
  constructor november-candidate-boundary
  field
    concreteNovemberCandidateLocated : Bool
    filenameRetained : Bool
    directLinkRetained : Bool
    sourceRoleSeparated : Bool
    productionIdentityPaid : Bool
open NovemberCandidateBoundary public

canonicalNovemberCandidateBoundary : NovemberCandidateBoundary
canonicalNovemberCandidateBoundary =
  november-candidate-boundary true true true true false
