module DASHI.Finance.TrumpSpaceXPrimaryAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradeSourceAtlas2026SupplementExact as Supplement

------------------------------------------------------------------------
-- SPACEX PRIMARY-ROW ACQUISITION FRONTIER
--
-- Reuters (2026-08-24) reports a June 23 purchase, a $15,001-$50,000 disclosure
-- range, a filing signed August 12 and made public August 22. The exact OGE
-- transaction row/primary artifact was not recovered in this acquisition pass.
-- OGE's public guidance confirms that Form 278-T is the periodic-transaction
-- record type and that public access is governed through the statutory Form-201
-- access mechanism. The secondary synthesis therefore remains paid while the
-- same-object primary row remains explicit debt.
------------------------------------------------------------------------

reutersSpaceXClaim : Atlas.TradeEvidenceClaim
reutersSpaceXClaim = Supplement.trumpSpaceXReutersSecondary

ogePublicDisclosureGuideArtifact : Source.SourceArtifact
ogePublicDisclosureGuideArtifact =
  Source.sourceArtifact
    "OGE-public-financial-disclosure-FAQ-2026"
    Source.documentaryArtifact
    "https://extapps2.oge.gov/web/OGE.nsf/publicresources_disclosure-faq"
    "U.S. Office of Government Ethics"

ogeForm201AccessArtifact : Source.SourceArtifact
ogeForm201AccessArtifact =
  Source.sourceArtifact
    "OGE-Form-201-public-access"
    Source.externalSystemArtifact
    "https://extapps2.oge.gov/201/Presiden.nsf/201%20Request"
    "U.S. Office of Government Ethics"

record SpaceXSecondaryFacts : Set where
  constructor spacex-secondary-facts
  field
    transactionDate : String
    disclosedRange : String
    filingSignedDate : String
    publicReleaseDate : String
    reportDate : String
    sourceReference : String

canonicalSpaceXSecondaryFacts : SpaceXSecondaryFacts
canonicalSpaceXSecondaryFacts =
  spacex-secondary-facts
    "2026-06-23"
    "$15,001-$50,000"
    "2026-08-12"
    "2026-08-22"
    "2026-08-24"
    "Reuters, 'Trump bought shares in Elon Musk's SpaceX in June, financial disclosure shows', 2026-08-24; no DOI"

record SpaceXPrimaryRowDebt : Set₁ where
  constructor spacex-primary-row-debt
  field
    secondaryClaim : Atlas.TradeEvidenceClaim
    secondarySynthesisPaid : Atlas.independentCorroborationPaid secondaryClaim ≡ true
    exactPrimaryTransactionRowPaid : Bool
    exactPrimaryTransactionRowPaidIsFalse : exactPrimaryTransactionRowPaid ≡ false
    primaryRecordTypeReference : String
    statutoryAccessReference : String
    exactRowLocatorNeeded : String
    sameObjectPromotionNeeded : String
    acquisitionReference : String

open SpaceXPrimaryRowDebt public

canonicalSpaceXPrimaryRowDebt : SpaceXPrimaryRowDebt
canonicalSpaceXPrimaryRowDebt =
  spacex-primary-row-debt
    reutersSpaceXClaim
    refl
    false refl
    "OGE Form 278-T is the periodic transaction report for covered purchases/sales/exchanges"
    "OGE Form 201 / Ethics in Government Act public-access mechanism"
    "recover exact Donald J. Trump 278-T row containing SpaceX purchase dated 2026-06-23 and its row/value-range locator"
    "bind Reuters secondary report to exact primary row before promoting same-object primary payment"
    "primary-row recovery remains open; search failure does not prove primary-row absence"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReutersReportAutomaticallyPaysPrimaryRow : Set where
data OGEAccessPathAutomaticallyPaysExactRow : Set where
data FilingDateAutomaticallyRevealsDecisionTimeInformation : Set where
data GovernmentContractorOwnershipAutomaticallyProvesConflictViolation : Set where

reutersDoesNotPayPrimaryRow : ReutersReportAutomaticallyPaysPrimaryRow → ⊥
reutersDoesNotPayPrimaryRow ()

accessPathDoesNotPayExactRow : OGEAccessPathAutomaticallyPaysExactRow → ⊥
accessPathDoesNotPayExactRow ()

filingDateDoesNotRevealDecisionInformation :
  FilingDateAutomaticallyRevealsDecisionTimeInformation → ⊥
filingDateDoesNotRevealDecisionInformation ()

ownershipDoesNotAutoProveConflictViolation :
  GovernmentContractorOwnershipAutomaticallyProvesConflictViolation → ⊥
ownershipDoesNotAutoProveConflictViolation ()

record SpaceXPrimaryAcquisitionBoundary : Set where
  constructor spacex-primary-acquisition-boundary
  field
    ReutersSecondaryIsPaid : Bool
    exactPrimaryRowRemainsDebt : Bool
    disclosureRangeIsNotExactNotional : Bool
    accessMechanismIsNotSameObjectReceipt : Bool
    transactionDoesNotRevealDecisionInformation : Bool
    transactionDoesNotProveConflictViolation : Bool

canonicalSpaceXPrimaryAcquisitionBoundary : SpaceXPrimaryAcquisitionBoundary
canonicalSpaceXPrimaryAcquisitionBoundary =
  spacex-primary-acquisition-boundary true true true true true true
