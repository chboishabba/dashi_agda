module DASHI.Law.AustralianMajorPartyDonationDisclosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Australian major-party donation/disclosure source surface.
--
-- This owner preserves the distinction among:
--   * party annual returns;
--   * donor annual returns;
--   * detailed receipts on party/associated-entity returns;
--   * party-specific voluntary disclosure policies; and
--   * any downstream inference about access, influence or policy causation.
--
-- A payment/receipt is evidence of a financial relation.  It is not, without
-- additional evidence, proof that a donor caused a policy position.
------------------------------------------------------------------------

data PartyFamily : Set where
  labor : PartyFamily
  liberal : PartyFamily

data DisclosureLayer : Set where
  aecPartyAnnualReturn : DisclosureLayer
  aecDonorAnnualReturn : DisclosureLayer
  aecDetailedReceipt : DisclosureLayer
  partyVoluntaryDisclosurePolicy : DisclosureLayer
  secondaryAECMirror : DisclosureLayer

data FinanceClaimKind : Set where
  statutoryThreshold : FinanceClaimKind
  voluntaryThreshold : FinanceClaimKind
  annualTotal : FinanceClaimKind
  disclosedReceipt : FinanceClaimKind
  crossPartyDonor : FinanceClaimKind
  causalInfluenceHypothesis : FinanceClaimKind

record FinanceReceipt : Set where
  constructor financeReceipt
  field
    party : PartyFamily
    layer : DisclosureLayer
    kind : FinanceClaimKind
    period : String
    sourceReference : String
    proposition : String
    causalSupport : Bool

open FinanceReceipt public

------------------------------------------------------------------------
-- Authoritative disclosure-system receipts checked 9 September 2026.
------------------------------------------------------------------------

aec2024Threshold : FinanceReceipt
aec2024Threshold = financeReceipt labor aecDetailedReceipt statutoryThreshold
  "2024-25"
  "AEC Transparency Register / Detailed Receipts; disclosure threshold $16,900"
  "For 2024-25, the Commonwealth disclosure threshold applicable to detailed receipts was $16,900."
  false

laborVoluntaryThreshold : FinanceReceipt
laborVoluntaryThreshold = financeReceipt labor partyVoluntaryDisclosurePolicy voluntaryThreshold
  "current page checked 2026-09-09"
  "Australian Labor Party, Donation disclosure"
  "Labor states a voluntary policy of disclosing all donations over $1,000, below the Commonwealth statutory threshold."
  false

liberalStatutoryThresholdSurface : FinanceReceipt
liberalStatutoryThresholdSurface = financeReceipt liberal partyVoluntaryDisclosurePolicy statutoryThreshold
  "2024-25"
  "Liberal Party of Australia, Electoral Act Compliance Confirmation Form"
  "The Liberal federal page states amounts received by the Federal Secretariat above $16,900 in 2024-25 were subject to Commonwealth disclosure."
  false

labor2024AnnualTotal : FinanceReceipt
labor2024AnnualTotal = financeReceipt labor aecPartyAnnualReturn annualTotal
  "2024-25"
  "AEC Political Party Annual Return, Australian Labor Party (ALP), returnId=80596"
  "The ALP federal annual return declared total receipts of $71,858,506; detailed receipts totalled $68,539,496."
  false

------------------------------------------------------------------------
-- Representative published donor/receipt coordinates.
-- These are examples from the published AEC surface (or mirrors explicitly
-- reproducing AEC data). They are not an exhaustive substitute for the live
-- Transparency Register export.
------------------------------------------------------------------------

westpacLabor : FinanceReceipt
westpacLabor = financeReceipt labor secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Westpac Banking Corporation"
  "Westpac disclosed multiple 2024-25 receipts/donations to Labor entities, including federal ALP entries."
  false

westpacLiberal : FinanceReceipt
westpacLiberal = financeReceipt liberal secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Westpac Banking Corporation"
  "Westpac disclosed multiple 2024-25 receipts/donations to Liberal entities, including the federal Liberal Party."
  false

macquarieLabor : FinanceReceipt
macquarieLabor = financeReceipt labor secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Macquarie Group"
  "Macquarie disclosed multiple 2024-25 receipts/donations to Labor entities."
  false

macquarieLiberal : FinanceReceipt
macquarieLiberal = financeReceipt liberal secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Macquarie Group"
  "Macquarie disclosed multiple 2024-25 receipts/donations to Liberal entities."
  false

woodsideLabor : FinanceReceipt
woodsideLabor = financeReceipt labor secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Woodside Energy Group"
  "Woodside disclosed 2024-25 receipts/donations to Labor entities."
  false

woodsideLiberal : FinanceReceipt
woodsideLiberal = financeReceipt liberal secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Woodside Energy Group"
  "Woodside disclosed 2024-25 receipts/donations to Liberal/National entities."
  false

sportsbetLabor : FinanceReceipt
sportsbetLabor = financeReceipt labor secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Sportsbet"
  "Sportsbet disclosed $71,500 to the federal ALP in 2024-25."
  false

sportsbetLiberal : FinanceReceipt
sportsbetLiberal = financeReceipt liberal secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Sportsbet"
  "Sportsbet disclosed $55,000 to the federal Liberal Party in 2024-25."
  false

meritonLabor : FinanceReceipt
meritonLabor = financeReceipt labor secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Meriton Properties"
  "Meriton disclosed $100,000 to the federal ALP in 2024-25."
  false

meritonLiberal : FinanceReceipt
meritonLiberal = financeReceipt liberal secondaryAECMirror disclosedReceipt
  "2024-25"
  "AEC-derived disclosure mirror: Meriton Properties"
  "Meriton disclosed $500,000 to the federal Liberal Party in 2024-25, plus additional Liberal-division receipts."
  false

------------------------------------------------------------------------
-- Cross-party finance boundary.
------------------------------------------------------------------------

record DonationCausationBoundary : Set where
  constructor donationCausationBoundary
  field
    disclosedDonationProvesAccess : Bool
    disclosedDonationProvesAccessIsFalse : disclosedDonationProvesAccess ≡ false
    disclosedDonationProvesPolicyCausation : Bool
    disclosedDonationProvesPolicyCausationIsFalse : disclosedDonationProvesPolicyCausation ≡ false
    sameDonorToBothPartiesProvesSamePolicy : Bool
    sameDonorToBothPartiesProvesSamePolicyIsFalse : sameDonorToBothPartiesProvesSamePolicy ≡ false
    financeRelationMayCreateInfluenceHypothesis : Bool
    financeRelationMayCreateInfluenceHypothesisIsTrue : financeRelationMayCreateInfluenceHypothesis ≡ true

canonicalDonationCausationBoundary : DonationCausationBoundary
canonicalDonationCausationBoundary = donationCausationBoundary false refl false refl false refl true refl
