module DASHI.Governance.PalantirEarlyIntelDevelopmentChronologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EARLY PALANTIR / INTELLIGENCE DEVELOPMENT CHRONOLOGY
--
-- The chronology distinguishes capital, customer access, product feedback,
-- beta/deployment evidence and programme-transfer claims.  Secondary histories
-- may pay chronology leads without manufacturing primary contract terms.
------------------------------------------------------------------------

wiredHistory : Source.AttributedSource
wiredHistory = Source.mkNoDOISource
  "Noah Shachtman"
  "Palantir Technologies spots patterns to solve crimes and track terrorists"
  "Wired"
  "2012"
  "https://www.wired.com/story/joining-the-dots/"
  Source.newsSource
  "near-primary company history: In-Q-Tel investment, CIA analyst access and iterative Palantir development; also reports Poindexter's account of meeting Karp/Thiel"
  Source.publicAttribution

randDissertation : Source.AttributedSource
randDissertation = Source.mkNoDOISource
  "RAND Pardee Graduate School dissertation"
  "Dissertation containing Palantir case chronology"
  "RAND Corporation"
  "2016"
  "https://www.rand.org/content/dam/rand/pubs/rgs_dissertations/RGSD300/RGSD378/RAND_RGSD378.pdf"
  Source.academicBookSource
  "strong secondary chronology: reports In-Q-Tel investment in September 2005, 2005-08 analyst refinement, an NCTC live-database beta test, and first government contracts by 2008"
  Source.publicAttribution

iqtPortfolio : Source.AttributedSource
iqtPortfolio = Source.mkNoDOISource
  "In-Q-Tel"
  "Portfolio: Palantir"
  "In-Q-Tel"
  "current portfolio surface accessed 2026"
  "https://www.iqt.org/portfolio?company-name=palantir"
  Source.institutionalSource
  "first-party portfolio identity only; does not independently pay original investment date, amount, contract scope, Wade participation or TIA continuity"
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "early Palantir intelligence-development chronology"
  "DASHI.Governance.PalantirEarlyIntelDevelopmentChronologyExact"
  (wiredHistory ∷ randDissertation ∷ iqtPortfolio ∷ [])
  "capital, intelligence-community customer access, analyst refinement, beta/deployment chronology and explicit non-transfer boundary"

data EventKind : Set where
  investment : EventKind
  customerAccess : EventKind
  productRefinement : EventKind
  betaDeployment : EventKind
  governmentContract : EventKind

record DevelopmentEvent : Set where
  constructor development-event
  field
    timeWindow : String
    kind : EventKind
    actorA : String
    actorB : String
    object : String
    source : Source.AttributedSource
    primaryReceipt : Bool
    boundedReading : String
    tiaTransferPaid : Bool

open DevelopmentEvent public

investment2005 : DevelopmentEvent
investment2005 = development-event
  "September 2005 reported"
  investment
  "In-Q-Tel"
  "Palantir"
  "equity investment / intelligence-community entry"
  randDissertation
  false
  "RAND reports a $2m September 2005 investment; retain as strong secondary chronology pending contemporaneous investment document."
  false

ciaRefinement2005To2008 : DevelopmentEvent
ciaRefinement2005To2008 = development-event
  "2005-2008 reported"
  productRefinement
  "Palantir engineers"
  "U.S. intelligence analysts"
  "test-drive and iterative product refinement"
  randDissertation
  false
  "secondary chronology reports sustained analyst interaction; this is product-development evidence, not TIA asset/code transfer."
  false

nctcBeta : DevelopmentEvent
nctcBeta = development-event
  "within 2005-2008 development period"
  betaDeployment
  "Palantir prototype"
  "National Counterterrorism Center"
  "reported beta test linked to live NCTC databases"
  randDissertation
  false
  "useful same-object acquisition lead; exact beta-test artefact, authorization and technical scope remain to be acquired."
  false

wiredCIAAccess : DevelopmentEvent
wiredCIAAccess = development-event
  "early development period"
  customerAccess
  "In-Q-Tel / CIA"
  "Palantir"
  "access to intended intelligence analysts and iterative feedback"
  wiredHistory
  false
  "near-primary history independently supports intelligence-customer access and refinement, without proving TIA succession."
  false

events : List DevelopmentEvent
events = investment2005 ∷ ciaRefinement2005To2008 ∷ nctcBeta ∷ wiredCIAAccess ∷ []

inQTel2005InvestmentChronologyPaid : Bool
inQTel2005InvestmentChronologyPaid = true

ciaAnalystRefinement2005To2008Paid : Bool
ciaAnalystRefinement2005To2008Paid = true

nctcLiveDatabaseBetaSecondaryReceiptPaid : Bool
nctcLiveDatabaseBetaSecondaryReceiptPaid = true

contemporaneousInvestmentAgreementPaid : Bool
contemporaneousInvestmentAgreementPaid = false

exactCIAContractScopePaid : Bool
exactCIAContractScopePaid = false

tiaAssetOrCodeTransferPaid : Bool
tiaAssetOrCodeTransferPaid = false

customerAccessMeansProgrammeTransfer : Bool
customerAccessMeansProgrammeTransfer = false

record EarlyDevelopmentBoundary : Set where
  constructor early-development-boundary
  field
    investmentProvesTIAIdentity : Bool
    analystFeedbackProvesAssetTransfer : Bool
    nctcBetaProvesTIAComponentIdentity : Bool
    secondaryChronologyProvesPrimaryContractTerms : Bool

canonicalEarlyDevelopmentBoundary : EarlyDevelopmentBoundary
canonicalEarlyDevelopmentBoundary = early-development-boundary false false false false
