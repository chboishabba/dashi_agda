module DASHI.Cognition.SpringfieldStateInfrastructureValueCaptureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SpringfieldLayeredValueCaptureParetoExact as Layered

------------------------------------------------------------------------
-- SPRINGFIELD STATE-INFRASTRUCTURE / PRIVATE-VALUE INCIDENCE
------------------------------------------------------------------------

data InfrastructureReceiptKind : Set where
  stateDeveloperAgreement : InfrastructureReceiptKind
  concessionalFinance : InfrastructureReceiptKind
  legislativeRecognition : InfrastructureReceiptKind
  publicInfrastructureAcceleration : InfrastructureReceiptKind

record InfrastructureReceipt : Set where
  constructor infrastructure-receipt
  field
    kind : InfrastructureReceiptKind
    source : String
    boundedFinding : String
    paid : Bool
open InfrastructureReceipt public

springfield1994AgreementReceipt : InfrastructureReceipt
springfield1994AgreementReceipt = infrastructure-receipt
  stateDeveloperAgreement
  "Queensland Competition Authority industry-assistance review; Queensland case law"
  "A 29 November 1994 agreement existed between the State, Springfield Land Corporation and Springfield Land Corporation (No. 2) Pty Ltd concerning accelerated social infrastructure for Springfield."
  true

springfieldProjectAgreementReceipt : InfrastructureReceipt
springfieldProjectAgreementReceipt = infrastructure-receipt
  legislativeRecognition
  "Cherish Enterprises Pty Ltd v Ipswich City Council [2017] QPEC 38; Local Government (Planning and Environment) Amendment Act 1995 references"
  "Case law records that legislatively identified 'Springfield Agreements' included the 1994 agreement and a 1995 'Springfield Project Agreement' concerning infrastructure for development of the same land. This pays existence/legislative recognition, not every contractual term."
  true

springfieldConcessionalFinanceReceipt : InfrastructureReceipt
springfieldConcessionalFinanceReceipt = infrastructure-receipt
  concessionalFinance
  "Queensland Competition Authority, Industry Assistance in Queensland 2015 Final Report Volume II"
  "The review states Springfield Land Corporation was obliged to contribute toward accelerated state social infrastructure; the outstanding contribution was payable upon creation of 10,000 residential allotments and treated as a CPI-indexed loan rather than a higher market-interest obligation. The QCA counted the interest differential as industry assistance."
  true

springfieldAssistanceEvaluationReceipt : InfrastructureReceipt
springfieldAssistanceEvaluationReceipt = infrastructure-receipt
  publicInfrastructureAcceleration
  "Queensland Competition Authority, Industry Assistance in Queensland 2015 Final Report Volume II"
  "The QCA classified the measure in construction-sector industry assistance and reported that the measure was not monitored and its economic impacts were not evaluated. This does not imply the arrangement was unlawful or net harmful."
  true

canonicalInfrastructureReceipts : List InfrastructureReceipt
canonicalInfrastructureReceipts =
  springfield1994AgreementReceipt ∷ springfieldProjectAgreementReceipt ∷
  springfieldConcessionalFinanceReceipt ∷ springfieldAssistanceEvaluationReceipt ∷ []

record PublicPrivateIncidence : Set where
  constructor public-private-incidence
  field
    privateLandValueCanBenefitFromAcceleratedInfrastructure : Bool
    publicSectorCanBearTimingAndFinancingExposure : Bool
    developerContributionCanCoexistWithPublicAssistance : Bool
    concessionalFinanceEqualsCorruption : Bool
    industryAssistanceProvesNetPrivateBenefit : Bool
    infrastructureAgreementProvesLaterPlanningOutcome : Bool
open PublicPrivateIncidence public

canonicalPublicPrivateIncidence : PublicPrivateIncidence
canonicalPublicPrivateIncidence = public-private-incidence
  true true true false false false

data ConcessionalFinanceImpliesCorruption : Set where
data AssistanceImpliesNetPrivateBenefit : Set where
data InfrastructureAgreementImpliesLaterPlanningOutcome : Set where

concessionalFinanceDoesNotCreateCorruption : ConcessionalFinanceImpliesCorruption → ⊥
concessionalFinanceDoesNotCreateCorruption ()

assistanceDoesNotAutoCloseNetBenefit : AssistanceImpliesNetPrivateBenefit → ⊥
assistanceDoesNotAutoCloseNetBenefit ()

agreementDoesNotCreateLaterOutcome : InfrastructureAgreementImpliesLaterPlanningOutcome → ⊥
agreementDoesNotCreateLaterOutcome ()

------------------------------------------------------------------------
-- Value-capture consequence.
--
-- Public acceleration can raise accessibility/service capacity and therefore
-- private option/land value.  The correct incidence question is not simply
-- whether the developer paid a contribution, but the discounted distribution
-- of costs, timing advantages, risk, land uplift and later recurring rents.
------------------------------------------------------------------------

record ValueCaptureQuestion : Set where
  constructor value-capture-question
  field
    publicCapitalOrTimingSupport : String
    privateContribution : String
    privateUpliftCoordinate : String
    unresolvedCounterfactual : String
open ValueCaptureQuestion public

springfieldInfrastructureValueQuestion : ValueCaptureQuestion
springfieldInfrastructureValueQuestion = value-capture-question
  "State acceleration of social infrastructure plus concessional CPI-indexed treatment of outstanding developer contribution."
  "Springfield Land Corporation contribution obligation tied to creation of 10,000 residential allotments."
  "Land/masterplan uplift, parcel-sale proceeds, development margin and downstream rent/option value made feasible or more valuable by accelerated infrastructure."
  "Quantify counterfactual timing, market-rate financing cost, actual repayments, public capital expenditure and parcel-level land uplift before estimating net transfer."
