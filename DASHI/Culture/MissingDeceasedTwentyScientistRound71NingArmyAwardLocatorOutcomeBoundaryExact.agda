module DASHI.Culture.MissingDeceasedTwentyScientistRound71NingArmyAwardLocatorOutcomeBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound26PrimaryLocatorPredecessorControlExact as R26

record NingArmyAwardReceipt : Set where
  constructor ning-army-award-receipt
  field
    agreementNumber : String
    title : String
    awardingOffice : String
    awardee : String
    statedGovernmentAmount : String
    scheduledEffectiveDate : String
    scheduledCompletionDate : String
    primaryReportLocator : String
    primaryBytesInCustody : Bool
    authoritativeFinalReportLocated : Bool
    boundary : String

open NingArmyAwardReceipt public

ningArmyAward : NingArmyAwardReceipt
ningArmyAward = ning-army-award-receipt
  "DAAH01-01-9-R001"
  "Gravito - Electro Magnetic Superconductivity Experiment"
  "US Army Aviation and Missile Command (AMCOM), AMSAM-AC-RD-BA"
  "AC Gravity LLC / historical transcription sometimes renders LLD; exact primary bytes should control spelling"
  "$448,970 stated government-dollar field in the reported FY2001 entry"
  "2001-04-25"
  "2002-09-25"
  "archived locator for Department of Defense, Annual Report on Cooperative Agreements and Other Transactions Entered into During FY2001 Under 10 USC 2371, historically cited as p. 66: https://web.archive.org/web/20210801183915id_/https://www.acq.osd.mil/dpap/Docs/FY01RPT.doc"
  false
  false
  "The locator and repeated transcriptions support award-entry discovery, but primary .doc bytes are not in current custody here. Scheduled dates and stated amount do not establish disbursement, technical completion, administrative closeout, validated result, or classification disposition."

armyAwardLocatorPaid : Bool
armyAwardLocatorPaid = true

primaryBytesCustodyPaid : Bool
primaryBytesCustodyPaid = false

authoritativeArmyFinalReportLocated : Bool
authoritativeArmyFinalReportLocated = false

scheduledDatesDoNotPayCompletion : Bool
scheduledDatesDoNotPayCompletion = true

statedAwardAmountDoesNotPayDisbursement : Bool
statedAwardAmountDoesNotPayDisbursement = true

noPublicFinalReportDoesNotPayClassification : Bool
noPublicFinalReportDoesNotPayClassification = true

noPublicFinalReportDoesNotPaySuccessOrFailure : Bool
noPublicFinalReportDoesNotPaySuccessOrFailure = true

secondaryConvergenceDoesNotReplacePrimaryCustody : Bool
secondaryConvergenceDoesNotReplacePrimaryCustody = true

separateNASAProgrammeCannotPayArmyOutcome : Bool
separateNASAProgrammeCannotPayArmyOutcome = true

round71H2PaidCount : Nat
round71H2PaidCount = 0

round71H3PaidCount : Nat
round71H3PaidCount = 0

round71Reading : String
round71Reading = "The Ning Li/AC Gravity Army branch has a strong exact locator: agreement DAAH01-01-9-R001 in the DoD FY2001 Other Transactions report trail, with an archived official-report URL and convergent historical transcriptions of the agreement title, Army AMCOM awarding office, stated $448,970 field, and scheduled dates. However, the primary legacy .doc bytes are not in current custody here and no authoritative public Army final report or closeout/result carrier was located in the bounded search. Therefore award-entry discovery is paid, while disbursement, prototype completion, administrative closeout, validated results and classification disposition remain unresolved. Missing public outcome records do not establish success, failure, concealment or classification."
