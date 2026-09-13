module DASHI.Culture.NingLiArmyTexasAuditPrimaryInspectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as A

------------------------------------------------------------------------
-- PRIMARY TEXAS AUDIT INSPECTION FOR DAAH01-01-9-R001
--
-- Two State of Texas statewide single-audit reports independently expose the
-- Army-style identifier in a Lockheed Martin pass-through row: FY2005 uses the
-- formatting DAAH01-01-9R001 and FY2006 uses DAAH01-01-9-R001.  This recurrence
-- is worth preserving, but it does not by itself establish that either Texas
-- pass-through row is the same administrative object as the reported AC Gravity
-- Other Transaction, nor does it establish a Lockheed -> AC Gravity relationship.
------------------------------------------------------------------------

texasFY2005Source : A.AttributedSource
texasFY2005Source = A.mkNoDOISource
  "Texas State Auditor's Office"
  "State of Texas Federal Portion of the Statewide Single Audit Report for the Fiscal Year Ended August 31, 2005"
  "Texas State Auditor report 06-325"
  "2006"
  "https://sao.texas.gov/Reports/Main/06-325.pdf"
  A.governmentSource
  "primary state-audit manifestation whose federal expenditure table displays a Lockheed Martin Corporation pass-through row with identifier DAAH01-01-9R001 and amount 17,529; the row is an accounting manifestation, not proof of AC Gravity identity, Army technical outcome or classified programme transfer"
  A.publicAttribution

texasFY2006Source : A.AttributedSource
texasFY2006Source = A.mkNoDOISource
  "Texas State Auditor's Office"
  "State of Texas Federal Portion of the Statewide Single Audit Report for the Fiscal Year Ended August 31, 2006"
  "Texas State Auditor report 07-316"
  "2007"
  "https://sao.texas.gov/Reports/Main/07-316.pdf"
  A.governmentSource
  "primary state-audit manifestation whose federal expenditure table displays a Lockheed Martin Corp pass-through row with identifier DAAH01-01-9-R001 and amount 477; table context remains required before welding the row to the reported AC Gravity Army agreement"
  A.publicAttribution

record TexasAuditAppearance : Set where
  constructor texas-audit-appearance
  field
    fiscalYear : String
    reportNumber : String
    passThroughEntity : String
    displayedIdentifier : String
    displayedAmount : String
    federalProgrammeContext : String
    sameObjectAsReportedACGravityAgreementPaid : Bool
    technicalOutcomePaid : Bool
    interpretation : String

open TexasAuditAppearance public

texasFY2005LockheedAppearance : TexasAuditAppearance
texasFY2005LockheedAppearance = texas-audit-appearance
  "2005"
  "06-325"
  "Lockheed Martin Corporation"
  "DAAH01-01-9R001"
  "17529"
  "Statewide single-audit federal expenditure schedule; exact recipient/programme row semantics still require full table inspection"
  false
  false
  "The identifier is a near-exact formatting variant of DAAH01-01-9-R001 and appears in a Lockheed pass-through row. This is a source-backed accounting occurrence, not a same-object or subcontract weld."

texasFY2006LockheedAppearance : TexasAuditAppearance
texasFY2006LockheedAppearance = texas-audit-appearance
  "2006"
  "07-316"
  "Lockheed Martin Corp"
  "DAAH01-01-9-R001"
  "477"
  "CFDA 12.420 Military Medical Research and Development table extraction in the statewide single-audit schedule; exact row/recipient semantics still require full table inspection"
  false
  false
  "The exact identifier recurs in the next fiscal-year audit under a Lockheed pass-through label. Recurrence makes a one-off OCR accident less attractive but still does not establish an AC Gravity/Lockheed relationship."

fy2005DisplayedAmount : String
fy2005DisplayedAmount = "17529"

fy2006DisplayedAmount : String
fy2006DisplayedAmount = "477"

record TexasAuditRecurrenceBoundary : Set where
  constructor texas-audit-recurrence-boundary
  field
    twoYearRecurrencePaysSameArmyObject : Bool
    twoYearRecurrencePaysLockheedACGravityRelationship : Bool
    twoYearRecurrenceWeakensPureOCRHypothesis : Bool
    amountEqualityRequiredForSameObject : Bool
    fullRowColumnContextRequired : Bool
    originalFY2001DoDRowStillRequired : Bool
    accountingAppearancePaysTechnicalOutcome : Bool

canonicalTexasAuditRecurrenceBoundary : TexasAuditRecurrenceBoundary
canonicalTexasAuditRecurrenceBoundary = texas-audit-recurrence-boundary
  false false true false true true false

twoYearRecurrencePaysSameArmyObject : Bool
twoYearRecurrencePaysSameArmyObject = false

twoYearRecurrenceWeakensPureOCRHypothesis : Bool
twoYearRecurrenceWeakensPureOCRHypothesis = true

lockheedACGravityRelationshipPaid : Bool
lockheedACGravityRelationshipPaid = false

nextAcquisition : String
nextAcquisition =
  "inspect the full FY2005 and FY2006 table headings/recipient rows and the original FY2001 DoD Other Transactions row; only then test whether the recurring identifier is the same Army agreement, a downstream subcontract/pass-through accounting reference, identifier reuse, or a table alignment artefact"
