module DASHI.Culture.MissingDeceasedRosterScopeReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedRosterExtensionNingLiNickPopeExact as Extension

------------------------------------------------------------------------
-- ROSTER SCOPE IS A FIRST-CLASS COORDINATE
--
-- The April-2026 House inquiry, later media/UAP rosters, historical antigravity
-- genealogy and China-comparison rosters are not interchangeable denominators.
-- A person can be scientifically important to the genealogy without belonging
-- to the House sequence described in the April 20 press release.
------------------------------------------------------------------------

data RosterScope : Set where
  houseApril2026Core
  expandedUAPNarrative
  historicalTechnicalGenealogy
  chinaMediaComparison : RosterScope

record ScopeReceipt : Set where
  constructor scope-receipt
  field
    scope : RosterScope
    sourceReference : String
    inclusionReading : String
    startingDateReading : String
    exactEnumeratedMembershipPaid : Bool
    maySupplyScientificDenominator : Bool
    maySupplyRoleInclusiveDenominator : Bool

open ScopeReceipt public

houseInquiryScope : ScopeReceipt
houseInquiryScope = scope-receipt
  houseApril2026Core
  "House Oversight and Government Reform press release, 2026-04-20: Comer & Burlison Seek Information on Missing Nuclear and Rocket Scientists"
  "investigates unconfirmed public reporting about scientists and other personnel connected to U.S. nuclear secrets or rocket technology; reports allege at least ten individuals"
  "press release describes the string as beginning in 2023 with Michael David Hicks"
  false
  false
  true

expandedNarrativeScope : ScopeReceipt
expandedNarrativeScope = scope-receipt
  expandedUAPNarrative
  "later media, UAP commentary and roster compilations"
  "may include historical anti-gravity researcher Ning Li and non-scientist UAP/civil-service figure Nick Pope in addition to the 2023-2026 U.S. science/personnel cases"
  "not one stable start date; narrative inclusion changes over time"
  false
  false
  true

historicalGenealogyScope : ScopeReceipt
historicalGenealogyScope = scope-receipt
  historicalTechnicalGenealogy
  "source-linked scientific genealogy used by DASHI"
  "includes older technical predecessors when needed to test mechanism/programme continuity, for example Ning Li/Li-Torr superconducting-gravity work"
  "historical technical objects may predate the event cohort by decades"
  true
  false
  false

chinaComparisonScope : ScopeReceipt
chinaComparisonScope = scope-receipt
  chinaMediaComparison
  "NewsNation and downstream reporting on Chinese scientist deaths"
  "separate comparison roster with unresolved >=10 versus nine named cardinality"
  "Chinese event dates are independent of the U.S. inquiry scope"
  false
  false
  true

ningLiPredatesHouseSequenceStart : Bool
ningLiPredatesHouseSequenceStart = true

nickPopeDoesNotEnterScientificDenominator : Bool
nickPopeDoesNotEnterScientificDenominator = true

scopeSpecificDenominatorRequired : Bool
scopeSpecificDenominatorRequired = true

ningLiExtensionPresent : Extension.ningLiRosterRepair ≡ Extension.ningLiRosterRepair
ningLiExtensionPresent = refl

nickPopeExtensionPresent : Extension.nickPopeRosterRepair ≡ Extension.nickPopeRosterRepair
nickPopeExtensionPresent = refl

record RosterScopeBoundary : Set where
  constructor roster-scope-boundary
  field
    houseCountEqualsExpandedNarrativeCount : Bool
    historicalTechnicalPredecessorAutomaticallyHouseCase : Bool
    nonScientistNarrativeFigureCountsAsScientist : Bool
    crossNationalComparisonMayReuseUSDenominator : Bool
    scopeMustBeFixedBeforeEnrichment : Bool
    scopeChangesMayBeStudiedAsNarrativeEvolution : Bool

canonicalRosterScopeBoundary : RosterScopeBoundary
canonicalRosterScopeBoundary = roster-scope-boundary
  false false false false true true
