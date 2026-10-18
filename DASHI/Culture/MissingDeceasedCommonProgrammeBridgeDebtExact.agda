module DASHI.Culture.MissingDeceasedCommonProgrammeBridgeDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COMMON-PROGRAMME BRIDGE DEBT
--
-- A known object/programme identifier is not yet an H2 edge.  This owner
-- records the shortest remaining documentary bridge from a source-backed
-- object to a literal same-object role receipt spanning retained scientists.
------------------------------------------------------------------------

data BridgePaymentClass : Set where
  primaryObjectCustody : BridgePaymentClass
  secondRetainedPersonIdentity : BridgePaymentClass
  sameObjectRoleReceipt : BridgePaymentClass
  preEventTemporalOverlap : BridgePaymentClass
  preEventOperationalReceipt : BridgePaymentClass

record BridgeDebtReceipt : Set where
  constructor bridge-debt-receipt
  field
    candidate : String
    anchorIdentifier : String
    currentPaidState : String
    nextPayment : BridgePaymentClass
    nextLiteralLeaf : String
    h2Distance : Nat
    h3Distance : Nat
    h2Paid : Bool
    h3Paid : Bool

open BridgeDebtReceipt public

ningArmyBridgeDebt : BridgeDebtReceipt
ningArmyBridgeDebt = bridge-debt-receipt
  "Ning Li / AC Gravity Army programme"
  "DAAH01-01-9-R001"
  "literal single-person programme identifier paid; primary archived FY2001 row/SOW bytes not yet inspected here"
  primaryObjectCustody
  "inspect original FY2001 row/SOW/closeout, then enumerate named personnel, facilities, subcontractors and apparatus identifiers for a second retained-person weld"
  2 4 false false

amyNingBridgeDebt : BridgeDebtReceipt
amyNingBridgeDebt = bridge-debt-receipt
  "Amy Eskridge -> Ning Li historical-reference path"
  "HAL5-Dec2018-Talk-AntiGravity.pdf / Ning Li & Doug Torr AC Gravity slide"
  "literal Amy-to-Ning historical work reference paid; shared programme membership unpaid"
  sameObjectRoleReceipt
  "inspect Amy Institute/NASA-reviewed release object and correspondence for AC Gravity, DAAH01-01-9-R001, apparatus, personnel or successor-programme identifiers"
  2 4 false false

rezaMcCaslandBridgeDebt : BridgeDebtReceipt
rezaMcCaslandBridgeDebt = bridge-debt-receipt
  "Reza/Hardwick Mondaloy -> AFRL -> McCasland"
  "FA930020P5032 plus McCasland AFRL Commander 2011-2013"
  "later AFRL Mondaloy procurement and command chronology separately paid; direct Reza/McCasland same-work-package role unpaid"
  sameObjectRoleReceipt
  "recover pre-2013 Mondaloy AFRL contract, programme review, briefing, approval or tasking record naming McCasland and a Reza/Hardwick programme object"
  2 4 false false

jplBridgeDebt : BridgeDebtReceipt
jplBridgeDebt = bridge-debt-receipt
  "Hicks/Maiwald JPL cluster"
  "JPL/Caltech"
  "shared institution paid; public science objects currently distinct"
  sameObjectRoleReceipt
  "locate one mission, instrument, facility, procurement or work-package identifier naming both Hicks and Maiwald or their exact components"
  1 3 false false

nudtBridgeDebt : BridgeDebtReceipt
nudtBridgeDebt = bridge-debt-receipt
  "Chen/Feng/Zhang Daibing NUDT cluster"
  "National University of Defense Technology"
  "shared strategic institution paid; exact technical objects currently distinct"
  sameObjectRoleReceipt
  "locate one PLA/NUDT task, project, laboratory, codebase or work-package identifier naming at least two retained scientists"
  1 3 false false

bridgePareto : List BridgeDebtReceipt
bridgePareto =
  jplBridgeDebt ∷ nudtBridgeDebt ∷ ningArmyBridgeDebt ∷ amyNingBridgeDebt ∷ rezaMcCaslandBridgeDebt ∷ []

objectIdentifierPaysSecondRetainedPerson : Bool
objectIdentifierPaysSecondRetainedPerson = false

historicalReferencePaysSharedProgramme : Bool
historicalReferencePaysSharedProgramme = false

commandAuthorityPaysSpecificProgrammeRole : Bool
commandAuthorityPaysSpecificProgrammeRole = false

laterProcurementPaysEarlierPersonalParticipation : Bool
laterProcurementPaysEarlierPersonalParticipation = false

h2RequiresLiteralSameObjectRoleReceipt : Bool
h2RequiresLiteralSameObjectRoleReceipt = true

h3RequiresPreEventOperationalReceipt : Bool
h3RequiresPreEventOperationalReceipt = true

currentH2BridgeCount : Nat
currentH2BridgeCount = 0

currentH3OperationalBridgeCount : Nat
currentH3OperationalBridgeCount = 0

nextBridgePareto : String
nextBridgePareto =
  "first pay exact JPL/NUDT same-work-package identities if public; in parallel inspect DAAH01-01-9-R001 primary bytes and pre-2013 Mondaloy programme records; only after an H2 bridge exists search pre-event operational/security linkage"
