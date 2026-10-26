module DASHI.Cognition.SpringfieldMaxCutWebPromotion20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SPRINGFIELD MAX-CUT SAME-OBJECT WEB PROMOTIONS — 2026-10-14
--
-- This owner promotes only propositions materially stronger than the prior
-- receipt round.  It does not use chronology to manufacture ownership or
-- lobbying causation.
------------------------------------------------------------------------

record Promotion : Set where
  constructor promotion
  field
    label : String
    source : String
    boundedFinding : String
    paid : Bool
open Promotion public

allgasSpringfieldParliament2005 : Promotion
allgasSpringfieldParliament2005 = promotion
  "Allgas/Energex Springfield same-object rollout"
  "Queensland Parliament weekly Hansard, 27 October 2005"
  "A Queensland parliamentary record states that Energex, through its subsidiary Allgas Energy Pty Ltd, planned to extend its natural-gas network to the new master-planned community of Springfield. This materially closes the identity bridge between the Springfield gas rollout and the Energex/Allgas network, but does not identify exact mains, easements or later transfer schedules."
  true

springfieldTreasurerProjectUpdateApril2025 : Promotion
springfieldTreasurerProjectUpdateApril2025 = promotion
  "Springfield/Santoro Treasurer-Energy-Home Ownership project update"
  "Queensland Treasurer/Energy/Home Ownership Chief of Staff diary, 9 April 2025"
  "The diary records Raynuha Sinnathamby and Ian Murray of Springfield City Group with Santo Santoro for an 'Introduction and update on project'. This pays a project-level lobbying subject coordinate in a portfolio spanning Treasury, Energy and Home Ownership; the diary does not identify which project, requested action or decision."
  true

springfieldTAFEPremisesApril2025 : Promotion
springfieldTAFEPremisesApril2025 = promotion
  "Springfield/Santoro TAFE-premises lobbying subject"
  "Queensland Chief of Staff diary, 10 April 2025"
  "The diary records Santo Santoro and Springfield City Group CEO Richard Eden in a meeting expressly described as 'Discussion on TAFE premises, Springfield'. This pays a concrete education/property/infrastructure lobbying subject, not an outcome, benefit, impropriety or gas connection."
  true

mirvacOrionLongitudinalAssetReceipt : Promotion
mirvacOrionLongitudinalAssetReceipt = promotion
  "Mirvac Orion long-run asset/value chronology"
  "Mirvac annual/interim property reports 2014-2026"
  "Mirvac financial reports repeatedly identify Orion Springfield Central and separate Orion Springfield land with an August 2002 acquisition date; the current portfolio reports 100% ownership and a 30 June 2026 valuation of AUD 518 million including sundry vacant land. This strengthens continuity of Mirvac's asset/land position but still does not expose the original 2002 Springfield-side sale/development instrument."
  true

record PromotionBoundary : Set where
  constructor promotion-boundary
  field
    allgasSpringfieldIdentityPaid : Bool
    exactSpringfieldGasAssetSchedulePaid : Bool
    projectLobbyingSubjectPaid : Bool
    tafeLobbyingSubjectPaid : Bool
    gasSpecificLobbyingAskPaid : Bool
    lobbyingOutcomePaid : Bool
    originalOrionInstrumentPaid : Bool
open PromotionBoundary public

canonicalPromotionBoundary : PromotionBoundary
canonicalPromotionBoundary = promotion-boundary
  true false true true false false false

data AllgasSpringfieldIdentityImpliesExactAssetTitle : Set where
data PortfolioNameImpliesGasAsk : Set where
data LobbyingSubjectImpliesOutcome : Set where
data LongitudinalAssetReceiptImpliesOriginalContractTerms : Set where

allgasIdentityDoesNotCreateExactAssetTitle : AllgasSpringfieldIdentityImpliesExactAssetTitle → ⊥
allgasIdentityDoesNotCreateExactAssetTitle ()

portfolioNameDoesNotCreateGasAsk : PortfolioNameImpliesGasAsk → ⊥
portfolioNameDoesNotCreateGasAsk ()

lobbyingSubjectDoesNotCreateOutcome : LobbyingSubjectImpliesOutcome → ⊥
lobbyingSubjectDoesNotCreateOutcome ()

longitudinalReceiptDoesNotCreateContractTerms : LongitudinalAssetReceiptImpliesOriginalContractTerms → ⊥
longitudinalReceiptDoesNotCreateContractTerms ()
