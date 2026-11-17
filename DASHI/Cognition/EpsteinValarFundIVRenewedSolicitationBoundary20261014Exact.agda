module DASHI.Cognition.EpsteinValarFundIVRenewedSolicitationBoundary20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- VALAR FUND IV: DECLINE -> RENEWED SOLICITATION/DILIGENCE — 2026-10-14
--
-- Fund IV is deliberately not promoted to a completed Southern Trust LP edge.
-- Primary emails show an initial decline in 2017, direct manager pushback, and
-- renewed subscription-document/performance diligence in 2018-19.
------------------------------------------------------------------------

data FundIVStage : Set where
  prospectiveLP : FundIVStage
  declined : FundIVStage
  managerReSolicitation : FundIVStage
  draftSubscription : FundIVStage
  performanceDiligence : FundIVStage
  acceptedSubscription : FundIVStage
  fundedCapitalCall : FundIVStage

record FundIVReceipt : Set where
  constructor fund-iv-receipt
  field
    label : String
    date : String
    source : String
    stage : FundIVStage
    boundedFinding : String
    paid : Bool
    completedInvestmentPaid : Bool
open FundIVReceipt public

fundIVInitialDecline : FundIVReceipt
fundIVInitialDecline = fund-iv-receipt
  "HBRK declines Fund IV"
  "2017-11-03"
  "EFTA01029050/51"
  declined
  "Richard Kahn replied to Valar's prospective-investor subscription materials that they were not interested in Fund IV."
  true false

mccormackPushback : FundIVReceipt
mccormackPushback = fund-iv-receipt
  "McCormack asks Epstein to reconsider Fund IV"
  "2017-11-03"
  "EFTA01029050"
  managerReSolicitation
  "Andrew McCormack wrote directly to Epstein after Kahn's decline, said Valar would love to have him as a partner again, emphasized that Funds II and III were doing very well, and asked why he was declining."
  true false

fundIVDraftPackage : FundIVReceipt
fundIVDraftPackage = fund-iv-receipt
  "Fund IV subscription agreement package"
  "2018-2019"
  "EFTA00810362; EFTA01016101; EFTA01028975"
  draftSubscription
  "Released Valar Fund IV subscription documents and McCormack/Epstein emails show renewed processing and diligence after the 2017 decline. The blank package explains the mechanics for becoming an LP but does not by itself show Southern Trust signed, was accepted or funded a call."
  true false

fundIVPerformanceDiligence : FundIVReceipt
fundIVPerformanceDiligence = fund-iv-receipt
  "Epstein asks about Fund IV/portfolio performance"
  "2019-02-05"
  "EFTA01028975 and related Valar correspondence"
  performanceDiligence
  "Epstein was still discussing Valar portfolio performance while Fund IV draft-subscription correspondence remained active, including N26 and other portfolio questions. This pays renewed diligence, not subscription acceptance."
  true false

fundIVSECExistence : FundIVReceipt
fundIVSECExistence = fund-iv-receipt
  "Valar Global Fund IV offering exists"
  "2018-09-24"
  "SEC Form D accession 0001726616-18-000001"
  prospectiveLP
  "Valar Global Fund IV LP and Valar Global Principals Fund IV LP filed a Form D in September 2018. This pays fund/offering identity independently of Epstein-specific participation."
  true false

record FundIVBoundary : Set where
  constructor fund-iv-boundary
  field
    initialDeclinePaid : Bool
    renewedSolicitationPaid : Bool
    renewedDiligencePaid : Bool
    completedSubscriptionPaid : Bool
    acceptedAsLPPaid : Bool
    capitalCallPaid : Bool
    draftDocumentsImplyInvestment : Bool
    performanceQuestionsImplyInvestment : Bool
open FundIVBoundary public

canonicalFundIVBoundary : FundIVBoundary
canonicalFundIVBoundary = fund-iv-boundary
  true true true false false false false false

data DraftSubscriptionImpliesLP : Set where
data DiligenceImpliesFundedInvestment : Set where
data PriorFundLPImpliesLaterFundLP : Set where

draftDoesNotCreateLP : DraftSubscriptionImpliesLP → ⊥
draftDoesNotCreateLP ()

diligenceDoesNotCreateFunding : DiligenceImpliesFundedInvestment → ⊥
diligenceDoesNotCreateFunding ()

priorFundsDoNotCreateFundIV : PriorFundLPImpliesLaterFundLP → ⊥
priorFundsDoNotCreateFundIV ()

data FundIVDebt : Set where
  executedSubscription : FundIVDebt
  gpAcceptance : FundIVDebt
  commitmentAmount : FundIVDebt
  firstCapitalCall : FundIVDebt
  finalDeclineOrCloseout : FundIVDebt

record FundIVAcquisition : Set where
  constructor fund-iv-acquisition
  field
    debt : FundIVDebt
    priority : Nat
    question : String
open FundIVAcquisition public

canonicalFundIVAcquisition : List FundIVAcquisition
canonicalFundIVAcquisition =
  fund-iv-acquisition executedSubscription 100
    "Search for a Southern Trust/related-entity signed Fund IV subscription agreement rather than inferring participation from draft documents."
  ∷ fund-iv-acquisition gpAcceptance 100
    "Find Valar GP acceptance/admission or LP capital-account statement naming the Epstein-side investor."
  ∷ fund-iv-acquisition commitmentAmount 99
    "Resolve any actual Fund IV commitment only after signed/accepted documents; do not import the USD10-20m Fund II pitch."
  ∷ fund-iv-acquisition firstCapitalCall 99
    "Search bank and capital-call records for a Fund IV wire; absence from the selected Deutsche Bank chart is not global noninvestment."
  ∷ fund-iv-acquisition finalDeclineOrCloseout 98
    "If no investment closed, acquire the final correspondence showing the renewed 2018-19 process ended without admission/funding."
  ∷ []
