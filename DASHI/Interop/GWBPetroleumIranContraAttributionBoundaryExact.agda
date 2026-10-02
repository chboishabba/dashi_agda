module DASHI.Interop.GWBPetroleumIranContraAttributionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB
import DASHI.Governance.IranContraCovertFlowHistoricalMechanismExact as IranContra

------------------------------------------------------------------------
-- GWB PETROLEUM / IRAN-CONTRA ATTRIBUTION BOUNDARY
--
-- Distinct fibres:
--   A. verified biographical petroleum background
--   B. verified Iran/Contra historical mechanism / archival record
--   C. local retained-book allegations in the GWB corpus
--
-- No fibre is allowed to promote another without a reviewed join.
------------------------------------------------------------------------

bush41OilBiography : Source.AttributedSource
bush41OilBiography = Source.mkNoDOISource
  "George H.W. Bush Presidential Library and Museum"
  "President George Bush / George H.W. Bush Papers - Zapata Oil Files"
  "Presidential Library / National Archives"
  ""
  "https://www.bush41library.gov/digital-research-room/finding-aid/george-h-w-bush-papers?naid=446394695"
  Source.governmentSource
  "primary archival/biographical source documenting Bush-Overbey, Zapata Petroleum and Zapata Offshore business records; not evidence of Iran-Contra involvement"
  Source.publicAttribution

bush41IranContraArchive : Source.AttributedSource
bush41IranContraArchive = Source.mkNoDOISource
  "George H.W. Bush Presidential Library and Museum"
  "Iran-Contra / Office of the Vice President and Counsel record series"
  "Presidential Library / National Archives"
  ""
  "https://www.bush41library.gov/digital-research-room/search"
  Source.governmentSource
  "archival finding-aid surface containing Iran-Contra OVP / VP-role files; existence of a record series is not a substantive finding about the contents of every file"
  Source.publicAttribution

record GWBCorpusAllegation : Set where
  constructor gwb-corpus-allegation
  field
    corpusRef : String
    retainedSourceRef : String
    propositionRef : String
    boundedReading : String
    corpusContainsClaim : Bool
    corpusContainsClaimIsTrue :
      corpusContainsClaim ≡ true
    claimIndependentlyVerified : Bool
    claimIndependentlyVerifiedIsFalse :
      claimIndependentlyVerified ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open GWBCorpusAllegation public

bushIranContraAllegation : GWBCorpusAllegation
bushIranContraAllegation =
  gwb-corpus-allegation
    "SensibLaw/demo/ingest/gwb/corpus_v1/wiki_timeline_gwb_corpus_v1.json"
    "Jeb and the Bush Crime Family (retained local-book lane)"
    "claim:book-alleges-bush-connection-to-iran-contra"
    "The retained book corpus contains an allegation of a Bush connection to Iran-Contra; the GWB audit says corpus snippets are noisy and candidate-world material is not historically trustworthy by default."
    true refl
    false refl
    true refl

record VerifiedBackground : Set where
  constructor verified-background
  field
    oilBiographyPaid : Bool
    oilBiographyPaidIsTrue : oilBiographyPaid ≡ true
    archivalIranContraSeriesPaid : Bool
    archivalIranContraSeriesPaidIsTrue :
      archivalIranContraSeriesPaid ≡ true
    historicalIranContraMechanismPaid : Bool
    historicalIranContraMechanismPaidIsTrue :
      historicalIranContraMechanismPaid ≡ true
    oilBiographyProvesIranContraParticipation : Bool
    oilBiographyProvesIranContraParticipationIsFalse :
      oilBiographyProvesIranContraParticipation ≡ false
    archiveSeriesProvesAllegation : Bool
    archiveSeriesProvesAllegationIsFalse :
      archiveSeriesProvesAllegation ≡ false

open VerifiedBackground public

canonicalBackground : VerifiedBackground
canonicalBackground =
  verified-background
    true refl
    true refl
    true refl
    false refl
    false refl

candidateWorld : GWB.GWBCandidateWorldBoundary
candidateWorld = GWB.canonicalGWBCandidateWorldBoundary

historicalMechanism : IranContra.HistoricalRoutingTopology
historicalMechanism = IranContra.iranContraTopology

data OilBiographyPlusIranContraEqualsOilCausalLink : Set where
data CorpusAllegationPlusArchiveSeriesEqualsVerifiedClaim : Set where
data CandidateWorldRelationMayPromoteWithoutReview : Set where
data RecordSeriesExistenceProvesFileContent : Set where

oilBiographyDoesNotCreateCausalLink :
  OilBiographyPlusIranContraEqualsOilCausalLink → ⊥
oilBiographyDoesNotCreateCausalLink ()

corpusAllegationDoesNotBecomeVerifiedByArchiveExistence :
  CorpusAllegationPlusArchiveSeriesEqualsVerifiedClaim → ⊥
corpusAllegationDoesNotBecomeVerifiedByArchiveExistence ()

candidateWorldMayNotPromoteWithoutReview :
  CandidateWorldRelationMayPromoteWithoutReview → ⊥
candidateWorldMayNotPromoteWithoutReview ()

recordSeriesDoesNotProveFileContent :
  RecordSeriesExistenceProvesFileContent → ⊥
recordSeriesDoesNotProveFileContent ()

oilSnowball :
  Snowball.SourceRoleSnowballReceipt bush41OilBiography
oilSnowball = Snowball.canonicalSourceRoleSnowballReceipt bush41OilBiography
