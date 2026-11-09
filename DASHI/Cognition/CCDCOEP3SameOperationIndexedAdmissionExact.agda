module DASHI.Cognition.CCDCOEP3SameOperationIndexedAdmissionExact where

------------------------------------------------------------------------
-- SAME-OPERATION, SIX-STAGE SOURCE-INDEXED COGNITIVE-WARFARE ADMISSION
--
-- Attribution: GCC original media and policy correspondence 1993;
-- 1998 API Global Climate Science Communications Team proposal is
-- a DIFFERENT original source, author set and time. The 2017
-- Supran/Oreskes analysis is an independent published corpus.
-- Rensberger, Hansen and film creators retain original authorship.
--
-- DASHI only proves dependent-type source/nonpromotion obligations.
-- No source bytes, calibrated effects, hostile purpose or original
-- historical operation witness is manufactured by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data OriginalCase : Set where
  gcc1993 : OriginalCase
  apiProposal1998 : OriginalCase
  exxonCorpus2017 : OriginalCase
  fictionalArt : OriginalCase

data EvidenceStage : Set where
  originalIntervention : EvidenceStage
  recipientExposure : EvidenceStage
  cognitiveMechanism : EvidenceStage
  causalDiscrimination : EvidenceStage
  independentlySourcedIntent : EvidenceStage
  originalAttribution : EvidenceStage

-- Evidence is a proposition indexed by original case AND stage. In
-- particular E gcc1993 recipientExposure does not supply
-- E apiProposal1998 recipientExposure by definitional conversion.
-- An external instantiation must still justify original provenance.
record AdmitsOneOriginalCase
    (E : OriginalCase → EvidenceStage → Set)
    (c : OriginalCase) : Set where
  field
    intervention : E c originalIntervention
    exposure : E c recipientExposure
    mechanism : E c cognitiveMechanism
    causal : E c causalDiscrimination
    intent : E c independentlySourcedIntent
    attribution : E c originalAttribution

-- Reuse of an admitted operation can project evidence for its SAME
-- case and SAME stage, not evidence about a different campaign.
sameCaseExposure :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  AdmitsOneOriginalCase E c → E c recipientExposure
sameCaseExposure E c admitted =
  AdmitsOneOriginalCase.exposure admitted

sameCaseIntent :
  (E : OriginalCase → EvidenceStage → Set)
  (c : OriginalCase) →
  AdmitsOneOriginalCase E c → E c independentlySourcedIntent
sameCaseIntent E c admitted =
  AdmitsOneOriginalCase.intent admitted

gccCaseNot1998Proposal :
  gcc1993 ≡ apiProposal1998 → ⊥
gccCaseNot1998Proposal ()

gccCaseNot2017Corpus :
  gcc1993 ≡ exxonCorpus2017 → ⊥
gccCaseNot2017Corpus ()

originalCaseNotFiction :
  gcc1993 ≡ fictionalArt → ⊥
originalCaseNotFiction ()

exposureIsNotIntent :
  recipientExposure ≡ independentlySourcedIntent → ⊥
exposureIsNotIntent ()

sourceTextIsNotCausalEffect :
  originalIntervention ≡ causalDiscrimination → ⊥
sourceTextIsNotCausalEffect ()

data CaseStage (c : OriginalCase) : Set where
  caseStage : (stage : EvidenceStage) → CaseStage c

-- A claim can carry both dimensions without losing the distinction
-- between author/campaign identity and observation/effect stage.
indexedClaim : (c : OriginalCase) → (stage : EvidenceStage) → CaseStage c
indexedClaim c stage = caseStage stage

-- A projection across cases requires an explicit equality of cases.
transportCaseStage :
  {c d : OriginalCase} →
  c ≡ d → CaseStage c → CaseStage d
transportCaseStage refl x = x

-- If an alleged transport from GCC 1993 to API 1998 explicitly
-- requires original-case identity, that assumption is contradictory.
noGCC1993ToAPI1998IdentityTransport :
  (gcc1993 ≡ apiProposal1998) →
  CaseStage gcc1993 → CaseStage apiProposal1998
noGCC1993ToAPI1998IdentityTransport proof _ =
  transportCaseStage proof (indexedClaim gcc1993 originalIntervention)

-- This theorem does NOT assert all E are nontrivial: if callers set
-- every E c stage to the unit type, evidence still becomes trivial.
-- A scientific instance must supply externally verified, distinct,
-- source-indexed evidence predicates and original review receipts.
