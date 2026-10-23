module DASHI.Cognition.PalantirEarlyIntelligenceProductAcquisition20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Capability
import DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact as Cross

------------------------------------------------------------------------
-- EARLY PALANTIR INTELLIGENCE PRODUCT / ACQUISITION OBJECTS — 2026-10-15
--
-- This owner narrows the earlier generic In-Q-Tel/CIA-development debt with
-- bounded historical receipts.  RAND's Palantir rapid-acquisition case study
-- synthesises the contemporary In-Q-Tel/Wired/WSJ/JIEDDO record; Wired supplies
-- a near-primary company/user history.  These sources pay investment amount,
-- analyst co-development, a live-database beta-test object and early JIEDDO use.
-- They do not establish TIA succession, transfer of TIA code/assets, or CIA
-- ownership/control of Palantir.
------------------------------------------------------------------------

data EarlySurface : Set where
  inQTelInvestment : EarlySurface
  analystCoDevelopment : EarlySurface
  liveDatabaseBeta : EarlySurface
  earlyGovernmentContract : EarlySurface
  jieddoOperationalUse : EarlySurface
  productCapabilityRefinement : EarlySurface

record EarlyReceipt : Set where
  constructor early-receipt
  field
    label : String
    date : String
    source : String
    surface : EarlySurface
    boundedFinding : String
    amountUSD : Nat
    paid : Bool
    primaryInstrumentPaid : Bool
    programmeSuccessionPaid : Bool
open EarlyReceipt public

iqtInvestment2005 : EarlyReceipt
iqtInvestment2005 = early-receipt
  "In-Q-Tel investment in Palantir"
  "2005-09"
  "Jonathan P. Wong, RAND/Pardee dissertation Palantir case study (2016), citing In-Q-Tel portfolio; Wired 2012 independently describes a roughly GBP1.3m In-Q-Tel investment"
  inQTelInvestment
  "The RAND case study records In-Q-Tel investing USD2m in Palantir in September 2005. Wired independently describes the investment as about GBP1.3m and emphasizes that its larger significance was access to intelligence analysts. This pays a bounded historical financing amount/date from a reputable secondary synthesis; the original investment agreement, equity/security terms and cap-table entry remain open."
  2000000 true false false

analystDevelopment2005_08 : EarlyReceipt
analystDevelopment2005_08 = early-receipt
  "Intelligence-analyst iterative product development"
  "2005-2008"
  "RAND case study; Wired 2012 'Joining the Dots'"
  analystCoDevelopment
  "RAND records Palantir engineers working with intelligence analysts from 2005-08 to test-drive and refine the product. Wired reports In-Q-Tel put the founders in front of frontline analysts and Karp estimated more than 300 likely-user meetings, with repeated software changes based on feedback."
  0 true false false

nctcLiveDatabaseBeta : EarlyReceipt
nctcLiveDatabaseBeta = early-receipt
  "National Counterterrorism Center live-database beta"
  "2005-2008"
  "RAND Palantir case study"
  liveDatabaseBeta
  "RAND states that one beta test linked a Palantir prototype to live databases in the Director of National Intelligence's National Counterterrorism Center. This identifies a concrete development/test object rather than only generic CIA adjacency. It does not establish transfer of TIA assets or NCTC procurement authority over later deployments."
  0 true false false

ciaCounterterrorismAudition : EarlyReceipt
ciaCounterterrorismAudition = early-receipt
  "CIA counterterrorism-centre unpaid audition"
  "pre-2008"
  "Wired 2012 'Joining the Dots'"
  productCapabilityRefinement
  "Wired reports that the CIA allowed Palantir to run software in its counterterrorism centre for several months without pay before Palantir had government revenue, as a capability audition. This pays a concrete early intelligence-community test environment while preserving the source's attribution and chronology."
  0 true false false

jieddo2008 : EarlyReceipt
jieddo2008 = early-receipt
  "JIEDDO early operational adoption"
  "2008"
  "RAND Palantir case study, citing JIEDDO annual report / Wired history"
  jieddoOperationalUse
  "RAND identifies JIEDDO among Palantir's first government clients and reports JIEDDO's 2008 annual report describing Palantir as supporting 600 investigations of IED networks. This pays early operational uptake after the intelligence-development phase; it does not make every later military Palantir programme a continuation of JIEDDO."
  0 true false false

record EarlyProductBoundary : Set where
  constructor early-product-boundary
  field
    iqInvestmentAmountDatePaid : Bool
    intelligenceAnalystFeedbackPaid : Bool
    nctcLiveDatabaseBetaPaid : Bool
    ciaCounterterrorismAuditionPaid : Bool
    earlyJieddoOperationalUsePaid : Bool
    originalIQTInvestmentInstrumentPaid : Bool
    tiaAssetOrCodeTransferPaid : Bool
    tiaProgrammeIdentityPaid : Bool
    ciaOperationalAuthorityOverPalantirPaid : Bool
    laterProcurementCausedByIQTPaid : Bool
open EarlyProductBoundary public

canonicalEarlyProductBoundary : EarlyProductBoundary
canonicalEarlyProductBoundary = early-product-boundary
  true true true true true false false false false false

data IQTInvestmentImpliesCIAControl : Set where
data LiveDatabaseBetaImpliesDatabaseOwnership : Set where
data EarlyUseImpliesLaterProgrammeContinuity : Set where
data AnalystFeedbackImpliesTIAAssetTransfer : Set where

iqtInvestmentDoesNotCreateCIAControl : IQTInvestmentImpliesCIAControl → ⊥
iqtInvestmentDoesNotCreateCIAControl ()

liveBetaDoesNotCreateDatabaseOwnership : LiveDatabaseBetaImpliesDatabaseOwnership → ⊥
liveBetaDoesNotCreateDatabaseOwnership ()

earlyUseDoesNotCreateLaterContinuity : EarlyUseImpliesLaterProgrammeContinuity → ⊥
earlyUseDoesNotCreateLaterContinuity ()

analystFeedbackDoesNotCreateTIAAssetTransfer : AnalystFeedbackImpliesTIAAssetTransfer → ⊥
analystFeedbackDoesNotCreateTIAAssetTransfer ()

------------------------------------------------------------------------
-- Remaining acquisition is now instrument/transfer specific.
------------------------------------------------------------------------

data EarlyDebt : Set where
  originalIQTFinancingInstrument : EarlyDebt
  palantirCapTable2005 : EarlyDebt
  nctcBetaTechnicalScope : EarlyDebt
  ciaAuditionTechnicalRecords : EarlyDebt
  jieddoContractAndRequirements : EarlyDebt
  tiaSuccessorAssetCodeRequirementJoin : EarlyDebt

record EarlyAcquisition : Set where
  constructor early-acquisition
  field
    debt : EarlyDebt
    priority : Nat
    instruction : String
open EarlyAcquisition public

canonicalEarlyAcquisition : List EarlyAcquisition
canonicalEarlyAcquisition =
  early-acquisition originalIQTFinancingInstrument 100
    "Acquire the original In-Q-Tel investment/security agreement, amendments and related development/customer-access terms; the USD2m historical amount is paid but the security and contractual rights are not." ∷
  early-acquisition palantirCapTable2005 100
    "Recover the 2005 Palantir cap table/security class to distinguish economic ownership, information rights, board rights and customer-development access." ∷
  early-acquisition nctcBetaTechnicalScope 99
    "Acquire technical/project records for the NCTC live-database beta: datasets, interfaces, prototype version, access controls, derived outputs and evaluation criteria." ∷
  early-acquisition ciaAuditionTechnicalRecords 99
    "Resolve the CIA counterterrorism-centre audition's exact dates, sponsor, product version, technical scope and evaluation/transition into a paid contract." ∷
  early-acquisition jieddoContractAndRequirements 99
    "Acquire JIEDDO's initial Palantir award/requirements and 2008 annual-report pages to pay contract scope and the reported 600-investigation use from a primary government carrier." ∷
  early-acquisition tiaSuccessorAssetCodeRequirementJoin 100
    "Independently test any TIA/IAO successor-component personnel, requirement, code, data-model or asset transfer into these early Palantir development objects. Functional similarity and chronology remain insufficient."
  ∷ []
