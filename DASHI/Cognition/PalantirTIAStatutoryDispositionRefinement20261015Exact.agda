module DASHI.Cognition.PalantirTIAStatutoryDispositionRefinement20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact as Cross

------------------------------------------------------------------------
-- TIA / IAO STATUTORY DISPOSITION REFINEMENT — 2026-10-15
--
-- 2003 disposition has two different continuation classes:
--   (1) named projects explicitly characterised by conferees as NOT components
--       of TIA for section 8131 and allowed to remain at DARPA;
--   (2) processing/analysis/collaboration tooling funded through the National
--       Foreign Intelligence Program under a classified-annex continuation.
--
-- Treating both as a single 'TIA successor' bucket destroys the exact object
-- needed for any later Palantir continuity claim.
------------------------------------------------------------------------

data DispositionClass : Set where
  darpaNonTIAContinuation : DispositionClass
  nfipCounterterrorismForeignIntelligenceContinuation : DispositionClass
  terminatedIAO : DispositionClass
  unresolvedClassifiedComponent : DispositionClass

record DispositionReceipt : Set where
  constructor disposition-receipt
  field
    label : String
    source : String
    class : DispositionClass
    boundedFinding : String
    paid : Bool
    palantirIdentityPaid : Bool
open DispositionReceipt public

iaoTermination : DispositionReceipt
iaoTermination = disposition-receipt
  "Information Awareness Office termination"
  "FY2004 DOD Appropriations conference material / section 8131 context"
  terminatedIAO
  "Congressional conference material eliminated DARPA TIA funding and directed termination of the Information Awareness Office. This is a statutory/programme disposition fact, not proof that every technical component ceased development everywhere."
  true false

bioALIRT : DispositionReceipt
bioALIRT = disposition-receipt
  "Bio-Event Advanced Leading Indicator Recognition Technology"
  "FY2004 conference report"
  darpaNonTIAContinuation
  "Conferees expressly listed Bio-ALIRT among projects allowed to continue at DARPA and stated that these named projects were not components of TIA for section 8131 purposes."
  true false

rapidAnalyticWargaming : DispositionReceipt
rapidAnalyticWargaming = disposition-receipt
  "Rapid Analytic Wargaming"
  "FY2004 conference report"
  darpaNonTIAContinuation
  "Rapid Analytic Wargaming was expressly permitted to continue at DARPA as a named non-TIA project for section 8131 purposes."
  true false

wargamingAsymmetricEnvironment : DispositionReceipt
wargamingAsymmetricEnvironment = disposition-receipt
  "Wargaming the Asymmetric Environment"
  "FY2004 conference report"
  darpaNonTIAContinuation
  "WAE was expressly permitted to continue at DARPA as a named non-TIA project for section 8131 purposes."
  true false

automatedSpeechText : DispositionReceipt
automatedSpeechText = disposition-receipt
  "Automated Speech and Text Exploitation in Multiple Languages"
  "FY2004 conference report"
  darpaNonTIAContinuation
  "ASTEM, including Babylon and Symphony, was expressly permitted to continue at DARPA and treated by conferees as outside TIA for section 8131."
  true false

nfipContinuation : DispositionReceipt
nfipContinuation = disposition-receipt
  "NFIP processing/analysis/collaboration continuation"
  "Public Law 108-87 section 8131; FY2004 Intelligence Authorization conference report / classified-annex description"
  nfipCounterterrorismForeignIntelligenceContinuation
  "Requested TIA funding was barred while funds were expressly provided through the National Foreign Intelligence Program for processing, analysis and collaboration tools for counterterrorism foreign intelligence. Public conference material says the classified annex specifically authorised continued development and encouraged participation by Intelligence Community elements. The public text does not name the classified programme/component/custodian objects."
  true false

record DispositionBoundary : Set where
  constructor disposition-boundary
  field
    iaoTerminationPaid : Bool
    namedDARPAContinuationsPaid : Bool
    namedDARPAProjectsClassifiedAsNonTIAByConferees : Bool
    nfipContinuationPaid : Bool
    publicNFIPComponentNamesPaid : Bool
    publicNFIPCustodianPaid : Bool
    palantirAsNFIPSuccessorPaid : Bool
    namedDARPAContinuationImpliesPalantirContinuity : Bool
    nfipFunctionalSimilarityImpliesPalantirContinuity : Bool
open DispositionBoundary public

canonicalDispositionBoundary : DispositionBoundary
canonicalDispositionBoundary = disposition-boundary
  true true true true false false false false false

data DARPAContinuationImpliesPalantir : Set where
data NFIPFunctionImpliesPalantir : Set where
data StatutoryContinuationImpliesAssetTransfer : Set where

darpaContinuationDoesNotCreatePalantir : DARPAContinuationImpliesPalantir → ⊥
darpaContinuationDoesNotCreatePalantir ()

nfipFunctionDoesNotCreatePalantir : NFIPFunctionImpliesPalantir → ⊥
nfipFunctionDoesNotCreatePalantir ()

statutoryContinuationDoesNotCreateAssetTransfer : StatutoryContinuationImpliesAssetTransfer → ⊥
statutoryContinuationDoesNotCreateAssetTransfer ()

------------------------------------------------------------------------
-- Residual is now the classified/NFIP object, not generic programme survival.
------------------------------------------------------------------------

data DispositionDebt : Set where
  classifiedAnnexProgrammeNames : DispositionDebt
  nfipExecutingElement : DispositionDebt
  nfipFundingLine : DispositionDebt
  transferredTIAComponentInventory : DispositionDebt
  personnelAndRequirementTransfer : DispositionDebt
  palantirSameObjectJoin : DispositionDebt

record DispositionAcquisition : Set where
  constructor disposition-acquisition
  field
    debt : DispositionDebt
    priority : Nat
    instruction : String
open DispositionAcquisition public

canonicalDispositionAcquisition : List DispositionAcquisition
canonicalDispositionAcquisition =
  disposition-acquisition classifiedAnnexProgrammeNames 100
    "Recover declassified/redacted annex, budget-justification, IG, congressional or programme-history records naming the NFIP processing/analysis/collaboration programme/components funded after TIA termination." ∷
  disposition-acquisition nfipExecutingElement 100
    "Identify the CIA/NSA/DIA/other executing element(s) and programme offices/custodians for the continued NFIP tooling rather than treating NFIP as a single agency." ∷
  disposition-acquisition transferredTIAComponentInventory 100
    "Build an exact inventory of TIA-linked code, prototypes, requirements, datasets or contracts transferred into the classified continuation; statutory funding continuity alone is not asset continuity." ∷
  disposition-acquisition nfipFundingLine 99
    "Resolve amounts and budget lines by component/year from declassified appropriations/authorisation records without inventing values hidden in the classified annex." ∷
  disposition-acquisition personnelAndRequirementTransfer 99
    "Resolve same-person programme authority and requirement continuity from IAO/TIA into the named NFIP continuation objects." ∷
  disposition-acquisition palantirSameObjectJoin 100
    "Only after the NFIP continuation is named, test whether Palantir's early CIA/NCTC/JIEDDO development touched that exact programme, code, requirement, personnel or contract object; functional resemblance and chronology remain insufficient."
  ∷ []
