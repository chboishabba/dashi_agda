module DASHI.Chemistry.HydrogenFuelCycleSourceAuthorityExact where

-- Evidence acquisition and attribution boundaries for the user-directed
-- fuel-regeneration investigation (2026-11-09), ChatGPT-drafted source.
-- Patent information is metadata to be verified against primary records,
-- NOT scientific proof or patent title adjudication.
--
-- Verified lookup anchor for US9809774B2:
-- https://patents.google.com/patent/US9809774B2/en
-- 2017-11-07, "Method of separating solids using bio-oils";
-- inventors Olev Trass and Michael David McLaren; Converde assignment
-- reel/frame 037501/0239 (recorded January 2016).
-- The source itself warns assignee/legal-status data may be incomplete.
--
-- These known claims must not be used to infer ownership of a distinct
-- unpublished patent or performance of an electrolysis/hydrogen apparatus.
-- US20150118145A1 names Gennadiy Glazunov; it is a distinct family.
-- A corporate transaction alone does not prove transfer of a particular
-- patent claim without a patent-specific asset schedule or title record.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data SourceStatus : Set where
  patentPublication : SourceStatus
  recordedAssignment : SourceStatus
  corporateDisclosure : SourceStatus
  vendorPerformanceClaim : SourceStatus
  meteredExperiment : SourceStatus
  independentlyReplicatedResult : SourceStatus

data ClaimKind : Set where
  attributionClaim : ClaimKind
  titleClaim : ClaimKind
  apparatusDescription : ClaimKind
  empiricalPerformance : ClaimKind

record PatentEvidence : Set where
  constructor patentEvidence
  field
    publicationNumber : String
    filingFamily : String
    primarySourceURL : String
    inventorsAsListed : String
    listedAssignee : String
    scopeOfClaims : String
    sourceKind : SourceStatus

open PatentEvidence public

knownBioOilGrant : PatentEvidence
knownBioOilGrant = patentEvidence
  "US9809774B2"
  "US14/894363; WO2014190420"
  "https://patents.google.com/patent/US9809774B2/en"
  "Olev Trass; Michael David McLaren"
  "Converde Energy Inc. (recorded; chain of title still requires checking)"
  "Method of separating solids using bio-oils; not identified as fuel synthesis"
  patentPublication

knownGlazunovApplication : PatentEvidence
knownGlazunovApplication = patentEvidence
  "US20150118145A1"
  "US provisional 61/970600 and 61/972088"
  "https://patents.google.com/patent/US20150118145A1/en"
  "Gennadiy Glazunov"
  "Assignment/licence relationships must be independently verified"
  "Ultra-pure hydrogen generation; separate from McLaren bio-oil claims"
  patentPublication

-- The new advertised grant was NOT positively located. A meaningful blank
-- cannot be promoted to a legal patent identifier by copying a company name.
data New2026GrantStatus : Set where
  grantUnresolved : New2026GrantStatus
  grantDocumentAcquired : New2026GrantStatus

current2026GrantStatus : New2026GrantStatus
current2026GrantStatus = grantUnresolved

grantUnresolvedIsNotAcquired :
  grantUnresolved ≡ grantDocumentAcquired → ⊥
grantUnresolvedIsNotAcquired ()

-- Typed evidence guards: no patent publication or vendor assertion can
-- be mistaken for the independent measurement class.
patentIsNotMeasured :
  patentPublication ≡ meteredExperiment → ⊥
patentIsNotMeasured ()

vendorIsNotIndependentlyReplicated :
  vendorPerformanceClaim ≡ independentlyReplicatedResult → ⊥
vendorIsNotIndependentlyReplicated ()

record PatentTitleReceipt : Set₁ where
  field
    specificPublicationNumber : String
    assignorAndAssigneeLegalIdentities : String
    executedConveyanceLocator : String
    patentAssetScheduleForThisPublication : Set
    fullChainAndJurisdictionPaid : Set
    independentRegisterConfirmation : Set

-- Corporate association, inventor identity and purchase announcement
-- are not sufficient to construct a PatentTitleReceipt.
