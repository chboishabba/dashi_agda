module DASHI.Culture.NingLiAdministrativeIdentifierCollisionParetoExact where

open import DASHI.Core.Prelude

import DASHI.Culture.MissingDeceasedIbrahimInvestigativeParetoExact as Base
import DASHI.Culture.NingLiArmyAgreementIdentifierCollisionExact as Collision

------------------------------------------------------------------------
-- Pareto specialization for the exact DAAH01-01-9-R001 administrative collision.
------------------------------------------------------------------------

ningLiAdministrativeIdentifierCollisionPareto : Base.InvestigativeParetoTarget
ningLiAdministrativeIdentifierCollisionPareto = Base.investigative-pareto-target
  Base.firstFront
  "Ning Li Army agreement identifier collision"
  "exact identifier -> source manifestation -> table/row semantics -> same-object test -> Army accounting/closeout genealogy"
  "inspect the original State of Texas 2006 single-audit table around DAAH01-01-9-R001 and determine the exact row/column alignment for the Lockheed Martin pass-through appearance; compare that administrative object against the original FY2001 DoD Other Transactions row before inferring any shared programme, subcontract, payment path or identifier reuse"
  "the Texas State Auditor report exposes the exact string DAAH01-01-9-R001 in a table extraction adjacent to a Lockheed Martin pass-through relationship and a small displayed amount; independent FY2001 source genealogy associates the same identifier with the reported AC Gravity prototype agreement, but the two manifestations are not yet welded"
  "whether the 2006 occurrence is a same-agreement pass-through/accounting residue, a subcontract reference, a table/OCR alignment artefact, a typo, or identifier reuse; whether it reveals any payment/prime/subrecipient relationship relevant to AC Gravity; whether the FY2001 row and later accounting state share the same administrative object"
  "DAAH01-01-9-R001; State of Texas Statewide Single Audit Report 07-316; DoD FY2001 Other Transactions report archived locator"
  "no person or programme QID may replace the administrative same-object test"
  "353 Public administration / 355 Military science / 657 Accounting / 629 Aerospace traversal only"
  "original Texas audit PDF/table coordinates, original FY2001 DoD row, Army accounting/payment records and any prime/subrecipient/subcontract documents carrying the identifier"
  true true false
  "First-front because one exact administrative disambiguation can either expose a previously unseen programme/accounting relationship or prune a misleading identifier collision. Equality of the identifier alone does not establish sameness, payment, Lockheed involvement, successful technology transfer or suppression."

existingCollisionBoundary : Collision.IdentifierCollisionBoundary
existingCollisionBoundary = Collision.canonicalIdentifierCollisionBoundary
