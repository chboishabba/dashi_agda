module DASHI.Cognition.QueenslandRinehartCrisafulliTrumpResourceAccessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- QUEENSLAND / RINEHART / CRISAFULLI / TRUMP RESOURCE-ACCESS OWNER
--
-- This owner separates:
--   * Rinehart -> Hanson/One Nation material support and policy advice;
--   * Rinehart -> Trump/Mar-a-Lago social/access brokerage;
--   * Crisafulli -> Trump-administration/Quad critical-minerals diplomacy;
--   * Queensland critical-minerals/resource fast-tracking;
-- while explicitly refusing to infer a Rinehart -> Crisafulli Trump-access edge
-- absent a direct source receipt.
------------------------------------------------------------------------

data QueenslandResourceAccessEdge : Set where
  rinehartCompanyAircraftToOneNation
  rinehartFundedHansonTravel
  rinehartPolicyAdviceToHanson
  rinehartOneNationRecruitmentAllegation
  crisafulliTrumpQuadPitch
  crisafulliCriticalMineralsPitch
  queenslandCriticalMineralsFastTrackLaw
  queenslandResourceFastTrackProgramme
  rinehartCrisafulliTrumpBrokerageUnpaid

record QueenslandResourceReceipt : Set where
  constructor queensland-resource-receipt
  field
    edge : QueenslandResourceAccessEdge
    sourceDescription : String
    relationPaid : Bool
    attributedOrDisputed : Bool
    wrongdoingEstablishedByThisReceipt : Bool
open QueenslandResourceReceipt public

aircraftReceipt : QueenslandResourceReceipt
aircraftReceipt = queensland-resource-receipt
  rinehartCompanyAircraftToOneNation
  "ABC 2026 reports a Rinehart company donated a new Cirrus G7 aircraft to One Nation; public reporting placed its listed value around AUD 1.3m. This is material campaign/logistics infrastructure, not policy capture."
  true false false

travelReceipt : QueenslandResourceReceipt
travelReceipt = queensland-resource-receipt
  rinehartFundedHansonTravel
  "ABC/Guardian 2026 report repeated flights and travel supplied or funded by Rinehart/Hancock/S. Kidman entities, including travel connecting to Florida/Mar-a-Lago events and later European travel disclosures."
  true false false

policyAdviceReceipt : QueenslandResourceReceipt
policyAdviceReceipt = queensland-resource-receipt
  rinehartPolicyAdviceToHanson
  "ABC 2026 records Pauline Hanson saying she consults Gina Rinehart on policy and that her pensioner-work proposal came from Rinehart. This pays policy input, not control over the party platform."
  true false false

recruitmentReceipt : QueenslandResourceReceipt
recruitmentReceipt = queensland-resource-receipt
  rinehartOneNationRecruitmentAllegation
  "ABC Four Corners 2026 reports Coalition sources saying Gina Rinehart asked Liberal MP Henry Pike whether he would consider joining One Nation; Pike regarded this as an attempt to recruit him. Rinehart did not substantively answer the specific recruitment question in that report."
  true true false

quadReceipt : QueenslandResourceReceipt
quadReceipt = queensland-resource-receipt
  crisafulliTrumpQuadPitch
  "AAP 2026 reports Queensland Premier David Crisafulli publicly pitching Queensland as host for a future Quad summit and explicitly discussing persuading Donald Trump to attend."
  true false false

criticalMineralsReceipt : QueenslandResourceReceipt
criticalMineralsReceipt = queensland-resource-receipt
  crisafulliCriticalMineralsPitch
  "AAP 2026 reports Crisafulli framing Queensland critical minerals as strategically valuable to the United States for military and advanced-technology supply chains."
  true false false

fastTrackLawReceipt : QueenslandResourceReceipt
fastTrackLawReceipt = queensland-resource-receipt
  queenslandCriticalMineralsFastTrackLaw
  "ABC 2026 reports Queensland enacted critical-minerals legislation granting expanded executive fast-track and compulsory-acquisition powers, including possible acquisition for private projects; government says safeguards remain and critics dispute adequacy."
  true true false

resourceProgrammeReceipt : QueenslandResourceReceipt
resourceProgrammeReceipt = queensland-resource-receipt
  queenslandResourceFastTrackProgramme
  "ABC 2026 reports the Crisafulli government separately pursued faster oil/gas approvals, coordinated-project treatment and state land/tender measures for fuel production/storage infrastructure."
  true false false

rinehartCrisafulliBoundaryReceipt : QueenslandResourceReceipt
rinehartCrisafulliBoundaryReceipt = queensland-resource-receipt
  rinehartCrisafulliTrumpBrokerageUnpaid
  "Current source sweep establishes separate Rinehart-Trump and Crisafulli-US/Trump-administration access paths but does not establish that Rinehart organised or facilitated Crisafulli's Trump diplomacy."
  false false false

record QueenslandResourceAccessBoundary : Set where
  constructor queensland-resource-access-boundary
  field
    rinehartMaterialSupportToOneNationPaid : Bool
    rinehartPolicyInputToHansonPaid : Bool
    rinehartAttemptedOneNationRecruitmentReported : Bool
    crisafulliTrumpDiplomacyPaid : Bool
    crisafulliCriticalMineralsDiplomacyPaid : Bool
    queenslandFastTrackResourceGovernancePaid : Bool
    rinehartBrokeredCrisafulliTrumpAccessPaid : Bool
    materialSupportProvesPolicyCapture : Bool
    policyAdviceProvesPartyControl : Bool
    parallelTrumpAccessProvesCoordination : Bool
open QueenslandResourceAccessBoundary public

canonicalQueenslandResourceAccessBoundary : QueenslandResourceAccessBoundary
canonicalQueenslandResourceAccessBoundary = queensland-resource-access-boundary
  true true true true true true false false false false

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data MaterialSupportImpliesPolicyCapture : Set where
data PolicyAdviceImpliesPartyControl : Set where
data ParallelTrumpAccessImpliesCoordination : Set where
data FastTrackLawImpliesCorruption : Set where
data ResourceAlignmentImpliesPrivateDirection : Set where

materialSupportDoesNotCreatePolicyCapture : MaterialSupportImpliesPolicyCapture → ⊥
materialSupportDoesNotCreatePolicyCapture ()

policyAdviceDoesNotCreatePartyControl : PolicyAdviceImpliesPartyControl → ⊥
policyAdviceDoesNotCreatePartyControl ()

parallelTrumpAccessDoesNotCreateCoordination : ParallelTrumpAccessImpliesCoordination → ⊥
parallelTrumpAccessDoesNotCreateCoordination ()

fastTrackLawDoesNotCreateCorruption : FastTrackLawImpliesCorruption → ⊥
fastTrackLawDoesNotCreateCorruption ()

resourceAlignmentDoesNotCreatePrivateDirection : ResourceAlignmentImpliesPrivateDirection → ⊥
resourceAlignmentDoesNotCreatePrivateDirection ()
