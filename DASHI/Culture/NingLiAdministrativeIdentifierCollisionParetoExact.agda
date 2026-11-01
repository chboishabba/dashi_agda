module DASHI.Culture.NingLiAdministrativeIdentifierCollisionParetoExact where

open import DASHI.Core.Prelude

import DASHI.Culture.MissingDeceasedIbrahimInvestigativeParetoExact as Base
import DASHI.Culture.NingLiArmyAgreementIdentifierCollisionExact as Collision
import DASHI.Culture.NingLiArmyTexasAuditPrimaryInspectionExact as Texas

------------------------------------------------------------------------
-- Pareto specialization for the exact DAAH01-01-9-R001 administrative collision.
------------------------------------------------------------------------

ningLiAdministrativeIdentifierCollisionPareto : Base.InvestigativeParetoTarget
ningLiAdministrativeIdentifierCollisionPareto = Base.investigative-pareto-target
  Base.firstFront
  "Ning Li Army agreement identifier collision"
  "exact identifier -> repeated audit manifestations -> table/row semantics -> same-object test -> Army accounting/closeout genealogy"
  "inspect the original State of Texas FY2005 and FY2006 single-audit tables around DAAH01-01-9R001 / DAAH01-01-9-R001 and determine the exact row/column, recipient and federal-programme semantics for the Lockheed Martin pass-through appearances; compare those administrative objects against the original FY2001 DoD Other Transactions row before inferring any shared programme, subcontract, payment path or identifier reuse"
  "the two-year Texas recurrence is source-backed: FY2005 report 06-325 shows a Lockheed Martin Corporation pass-through appearance with DAAH01-01-9R001 and displayed amount 17,529; FY2006 report 07-316 shows Lockheed Martin Corp with DAAH01-01-9-R001 and displayed amount 477; independent FY2001 source genealogy associates the same canonical identifier with the reported AC Gravity prototype agreement, but the manifestations are not yet welded"
  "whether the Texas occurrences are downstream accounting/pass-through references to the same Army agreement, a subcontract relationship, a table-alignment artefact, identifier reuse or another administrative object; whether any Lockheed/AC Gravity relationship actually exists; whether the FY2001 row and later accounting states share the same object"
  "DAAH01-01-9-R001; State of Texas reports 06-325 and 07-316; DoD FY2001 Other Transactions report archived locator"
  "no person or programme QID may replace the administrative same-object test"
  "353 Public administration / 355 Military science / 657 Accounting / 629 Aerospace traversal only"
  "full Texas table headings/recipient rows, original FY2001 DoD row, Army accounting/payment records and any prime/subrecipient/subcontract documents carrying the identifier"
  true true false
  "First-front because repeated independent state-audit appearances make a one-off OCR explanation less attractive while still leaving the substantive relationship unresolved. Equality or recurrence of the identifier does not establish sameness, payment, Lockheed involvement with AC Gravity, successful technology transfer or suppression."

existingCollisionBoundary : Collision.IdentifierCollisionBoundary
existingCollisionBoundary = Collision.canonicalIdentifierCollisionBoundary

existingTexasBoundary : Texas.TexasAuditRecurrenceBoundary
existingTexasBoundary = Texas.canonicalTexasAuditRecurrenceBoundary
