module DASHI.Governance.JohnPaperClaimManifestV2Exact where

------------------------------------------------------------------------
-- JOHN PAPER CLAIM MANIFEST V2
--
-- Source artifact: supplied draft
--   "Johns-Research-Paper_3_tracked changes.docx"
-- and supplied merged research manifest
--   "john_paper_claim_manifest_v2_merged.csv".
-- No DOI is asserted for either user-supplied artifact.
--
-- This module formalises the audit structure, not the truth of the manuscript.
-- A claim can have a well-supported construct/mechanism receipt while its
-- domain instantiation, etiology, or legal-elements receipt remains missing.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DependentReligiousEntrapmentCandidateExact as Entrapment
import DASHI.Governance.EvolvingCapacityReligiousAutonomyExact as CRC
import DASHI.Governance.CoercionConfinementLegalSeparationExact as Legal

record ClaimKey : Set where
  constructor claimKey
  field
    value : String

open ClaimKey public

data ReceiptKind : Set where
  constructReceipt domainInstantiationReceipt mechanismReceipt etiologyReceipt : ReceiptKind
  rightsReceipt legalElementsReceipt normativeReceipt sourceCorrectionReceipt : ReceiptKind

data ReceiptStatus : Set where
  installed missing rejectedUnlessNarrowed superseded unresolved : ReceiptStatus

record ClaimReceiptStatus : Set where
  constructor claimReceiptStatus
  field
    kind : ReceiptKind
    status : ReceiptStatus
    sourceOrReason : String

record ManifestClaim : Set where
  constructor manifestClaim
  field
    key : ClaimKey
    parentOrPrior : String
    claimText : String
    receipts : List ClaimReceiptStatus
    supersededBy : String
    boundedReading : String

open ManifestClaim public

------------------------------------------------------------------------
-- C005b-rev: entrapment construct versus Catholic-childhood instantiation.
------------------------------------------------------------------------

c005bRev : ManifestClaim
c005bRev = manifestClaim
  (claimKey "C005b-rev")
  "C005b"
  "coercive entrapment dynamics are a candidate mechanism under dependence, constrained exit, sanction and closure"
  ( claimReceiptStatus constructReceipt installed
      "Mary Landenburger, A process of entrapment in and recovery from an abusive relationship, 1989, DOI 10.3109/01612848909140846; Evan Stark, Coercive Control: The Entrapment of Women in Personal Life, 2007, DOI 10.1093/oso/9780195154276.001.0001"
  ∷ claimReceiptStatus domainInstantiationReceipt missing
      "the cited intimate-partner-abuse populations do not themselves instantiate Catholic-childhood exposure; require religion/family/exit/fear matched evidence"
  ∷ [] )
  ""
  "retain coercive-entrapment language as a construct/mechanism hypothesis; do not substitute false imprisonment and do not promote ordinary religious upbringing to entrapment"

------------------------------------------------------------------------
-- C003b: coercive-persuasion mechanism versus etiology.
------------------------------------------------------------------------

c003b : ManifestClaim
c003b = manifestClaim
  (claimKey "C003b")
  "C003"
  "coercive-persuasion dissociative mechanisms are clinically described, but a diagnosis does not establish its cause"
  ( claimReceiptStatus mechanismReceipt installed
      "mechanism/category receipt installed in the research manifest; retain exact DSM/source citation in the paper bibliography audit"
  ∷ claimReceiptStatus etiologyReceipt missing
      "personal diagnosis or narrative cannot establish etiology for a general developmental claim"
  ∷ [] )
  ""
  "mechanism existence and case etiology are separate proof obligations"

------------------------------------------------------------------------
-- C001c/C004b: CRC evolving-capacity correction.
------------------------------------------------------------------------

c001c : ManifestClaim
c001c = manifestClaim
  (claimKey "C001c")
  "C001"
  "religious formation should be analysed through capacity-sensitive participation, conscience/religion, guidance and evolving autonomy rather than a hard age-of-reason switch"
  ( claimReceiptStatus rightsReceipt installed
      "United Nations, Convention on the Rights of the Child, 1989, especially Articles 5, 12 and 14; treaty source, no DOI asserted"
  ∷ [] )
  ""
  "early formation before epistemic independence is relevant, but under-18 status does not prohibit religious exposure and age alone is not the competence theorem"

c004b : ManifestClaim
c004b = manifestClaim
  (claimKey "C004b")
  "C004"
  "child freedom of thought, conscience and religion is read with evolving capacities and parental guidance"
  ( claimReceiptStatus rightsReceipt installed
      "United Nations, Convention on the Rights of the Child, 1989, Articles 5 and 14; no DOI asserted"
  ∷ [] )
  ""
  "replaces use of a broad self-determination article as the most direct child-religious-autonomy authority"

------------------------------------------------------------------------
-- C005a: modern slavery remains elements-gated.
------------------------------------------------------------------------

c005a : ManifestClaim
c005a = manifestClaim
  (claimKey "C005a")
  "C005"
  "modern-slavery terminology requires offence-specific ownership/labour/services elements rather than coercion resemblance alone"
  ( claimReceiptStatus legalElementsReceipt rejectedUnlessNarrowed
      "Commonwealth of Australia, Criminal Code Act 1995, Division 270; legislation, no DOI asserted"
  ∷ [] )
  ""
  "mechanism resemblance does not satisfy legal elements; retain only if narrowed to an actually evidenced Division 270 category"

------------------------------------------------------------------------
-- Exact manifest promotion boundaries.
------------------------------------------------------------------------

data ConstructReceiptPromotesDomainInstantiation : Set where

data MechanismReceiptPromotesEtiology : Set where

data PersonalDiagnosisPromotesGeneralEtiology : Set where

data CoercionResemblancePromotesSlaveryElements : Set where

constructDoesNotPromoteDomainInstantiation :
  ConstructReceiptPromotesDomainInstantiation → ⊥
constructDoesNotPromoteDomainInstantiation ()

mechanismDoesNotPromoteEtiology : MechanismReceiptPromotesEtiology → ⊥
mechanismDoesNotPromoteEtiology ()

personalDiagnosisDoesNotPromoteGeneralEtiology :
  PersonalDiagnosisPromotesGeneralEtiology → ⊥
personalDiagnosisDoesNotPromoteGeneralEtiology ()

coercionDoesNotPromoteSlaveryElements :
  CoercionResemblancePromotesSlaveryElements → ⊥
coercionDoesNotPromoteSlaveryElements ()

record ManifestV2Boundary : Set where
  constructor manifestV2Boundary
  field
    constructAndApplicationSeparated : Bool
    mechanismAndEtiologySeparated : Bool
    originalAndRevisedClaimsLinked : Bool
    rightsModelUsesEvolvingCapacity : Bool
    legalElementsRemainJurisdictionSpecific : Bool
    personalNarrativeCreatesPopulationEtiology : Bool

canonicalManifestV2Boundary : ManifestV2Boundary
canonicalManifestV2Boundary =
  manifestV2Boundary true true true true true false
