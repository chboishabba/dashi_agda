module DASHI.Cognition.EpsteinThielValarDirectSolicitation20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinValarCapitalLedgerClosure20261014Exact as Valar

------------------------------------------------------------------------
-- DIRECT THIEL -> EPSTEIN -> VALAR SOLICITATION / INVESTMENT PATH
--
-- Primary emails pay a direct solicitation and introduction path.  The later
-- Southern Trust LP records pay investment.  They do not make Valar identical
-- to Palantir or establish a Palantir investment/contract/control edge.
------------------------------------------------------------------------

data DirectThielSurface : Set where
  directEmail : DirectThielSurface
  fundIntroduction : DirectThielSurface
  investmentRecommendation : DirectThielSurface
  futureInPersonDiscussion : DirectThielSurface
  fundraisingFollowup : DirectThielSurface
  realisedLPInvestment : DirectThielSurface

record DirectThielReceipt : Set where
  constructor direct-thiel-receipt
  field
    label : String
    date : String
    source : String
    surfaces : List DirectThielSurface
    boundedFinding : String
    directContactPaid : Bool
    completedInvestmentPaid : Bool
    palantirEdgePaid : Bool
open DirectThielReceipt public

thielIntroduction20141115 : DirectThielReceipt
thielIntroduction20141115 = direct-thiel-receipt
  "Thiel introduces Valar team and recommends allocation"
  "2014-11-15"
  "EFTA02594707 / duplicate thread EFTA01001339"
  (directEmail ∷ fundIntroduction ∷ investmentRecommendation ∷ futureInPersonDiscussion ∷ [])
  "Peter Thiel emailed Jeffrey Epstein directly, introduced Andrew McCormack and James Fitzgerald as his early-stage VC team, described Valar Ventures as the platform for a second fund, said it would make sense for Epstein to put USD10-20m into it, and offered to discuss further when they next met in person. This pays solicitation/introduction and an expectation of future in-person contact; it does not by itself prove that later meeting occurred."
  true false false

valarFollowup20141115 : DirectThielReceipt
valarFollowup20141115 = direct-thiel-receipt
  "Valar team fundraising follow-up"
  "2014-11-15"
  "EFTA01001339"
  (fundraisingFollowup ∷ fundIntroduction ∷ [])
  "Andrew McCormack replied to Epstein after Thiel's introduction, proposed an introductory phone call or in-person meeting, and attached Valar's fundraising deck."
  true false false

thielRecommendation20141218 : DirectThielReceipt
thielRecommendation20141218 = direct-thiel-receipt
  "Thiel direct follow-up recommendation"
  "2014-12-18"
  "EFTA01003346"
  (directEmail ∷ investmentRecommendation ∷ futureInPersonDiscussion ∷ [])
  "Responding to Epstein's 'valar? you?' email, Peter Thiel wrote that Epstein should definitely invest in Valar, recommended roughly USD10-20m, and asked where Epstein would be in January."
  true false false

southernTrustValarRealisation : DirectThielReceipt
southernTrustValarRealisation = direct-thiel-receipt
  "Southern Trust later becomes Valar II/III LP"
  "2015-2019"
  "Valar LP statements, capital calls and Deutsche Bank wire records formalised in EpsteinValarCapitalLedgerClosure20261014Exact"
  (realisedLPInvestment ∷ [])
  "Southern Trust subsequently took USD15m and USD25m commitments in Valar Global Funds II and III. This pays completion of a Valar investment after Thiel's direct solicitation; attribution of the causal decision solely to Thiel remains stronger than mere chronology but is not promoted beyond the direct solicitation-plus-completion path."
  true true false

record SolicitationRealisationBoundary : Set where
  constructor solicitation-realisation-boundary
  field
    thielDirectlySolicitedValarInvestment : Bool
    thielIntroducedFundTeam : Bool
    southernTrustLaterInvestedInValar : Bool
    directSolicitationPlusLaterInvestmentExists : Bool
    thisProvesPalantirInvestment : Bool
    thisProvesThielControlledSouthernTrust : Bool
    thisProvesEveryValarDecisionWasThielDirected : Bool
open SolicitationRealisationBoundary public

canonicalSolicitationRealisationBoundary : SolicitationRealisationBoundary
canonicalSolicitationRealisationBoundary = solicitation-realisation-boundary
  true true true true false false false

data ValarImpliesPalantir : Set where
data SolicitationImpliesInvestorControl : Set where
data LaterInvestmentImpliesEveryTermFromSolicitor : Set where
data ProposedMeetingImpliesCompletedMeeting : Set where

valarDoesNotCreatePalantir : ValarImpliesPalantir → ⊥
valarDoesNotCreatePalantir ()

solicitationDoesNotCreateInvestorControl : SolicitationImpliesInvestorControl → ⊥
solicitationDoesNotCreateInvestorControl ()

laterInvestmentDoesNotCreateAllTermCausation : LaterInvestmentImpliesEveryTermFromSolicitor → ⊥
laterInvestmentDoesNotCreateAllTermCausation ()

proposedMeetingDoesNotCreateCompletedMeeting : ProposedMeetingImpliesCompletedMeeting → ⊥
proposedMeetingDoesNotCreateCompletedMeeting ()

------------------------------------------------------------------------
-- Next same-object acquisition.
------------------------------------------------------------------------

data ThielValarDebt : Set where
  completed2014_2015Meeting : ThielValarDebt
  subscriptionNegotiationThread : ThielValarDebt
  sideLetterPrivileges : ThielValarDebt
  thielRoleInSpecificTerms : ThielValarDebt
  valarPortfolioLookThrough : ThielValarDebt
  palantirSpecificProposalOrInvestment : ThielValarDebt

record ThielValarAcquisition : Set where
  constructor thiel-valar-acquisition
  field
    debt : ThielValarDebt
    priority : Nat
    question : String
open ThielValarAcquisition public

canonicalThielValarAcquisition : List ThielValarAcquisition
canonicalThielValarAcquisition =
  thiel-valar-acquisition subscriptionNegotiationThread 100
    "Acquire the complete thread from Thiel's Nov/Dec 2014 solicitation through Valar diligence, allocation negotiation, subscription documents and the first January 2015 capital call."
  ∷ thiel-valar-acquisition sideLetterPrivileges 100
    "Resolve whether Southern Trust received fee breaks, capacity, co-investment, information, governance or other side-letter rights not shared by ordinary LPs."
  ∷ thiel-valar-acquisition completed2014_2015Meeting 99
    "Resolve the proposed Thiel/Epstein and Valar-team meetings into completed meeting receipts, dates and attendees rather than importing completion from scheduling language."
  ∷ thiel-valar-acquisition thielRoleInSpecificTerms 99
    "Determine whether Thiel personally negotiated allocation/terms after the initial recommendation or whether execution passed entirely to McCormack/Fitzgerald/Valar operations."
  ∷ thiel-valar-acquisition valarPortfolioLookThrough 98
    "Map Southern Trust's indirect portfolio exposure by fund and date from manager reports, preserving LP exposure versus portfolio-company control."
  ∷ thiel-valar-acquisition palantirSpecificProposalOrInvestment 97
    "Search independently for any Palantir-specific investment, proposal, introduction, service or governance edge; never derive it transitively from Thiel+Valar."
  ∷ []
