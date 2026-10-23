module DASHI.Cognition.SpringfieldLayeredValueCaptureClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.SpringfieldLayeredValueCaptureParetoExact as Prior
import DASHI.Cognition.SpringfieldValueCaptureReceiptRound20261014Exact as Receipts
import DASHI.Cognition.SpringfieldMaxCutWebPromotion20261014Exact as Promotion

------------------------------------------------------------------------
-- CLOSURE RECEIPT FOR THE 2026-10-14 SPRINGFIELD MAX-CUT ROUND
--
-- `closedAtLevel` is deliberately level-sensitive.  A network-level lineage,
-- subject-category receipt or transaction vehicle can be closed while a more
-- specific asset schedule, lobbying ask or beneficial-capital split remains
-- open.  This prevents a partially paid Pareto leaf from being treated as a
-- terminal proposition.
------------------------------------------------------------------------

data ClosureLevel : Set where
  identityLevel : ClosureLevel
  transactionLevel : ClosureLevel
  networkLevel : ClosureLevel
  subjectCategoryLevel : ClosureLevel
  instrumentLevel : ClosureLevel
  beneficialOwnershipLevel : ClosureLevel
  parcelIncidenceLevel : ClosureLevel

data SpringfieldLeaf : Set where
  cityWestAcquisitionVehicle : SpringfieldLeaf
  cityWestCapitalStack : SpringfieldLeaf
  springfieldGasNetworkLineage : SpringfieldLeaf
  springfieldExactGasAssets : SpringfieldLeaf
  santoroSpringfieldSubject : SpringfieldLeaf
  santoroSpecificAskDecision : SpringfieldLeaf
  mirvacOrionChronology : SpringfieldLeaf
  mirvacOriginalInstrument : SpringfieldLeaf
  masterDeveloperParcelActivity : SpringfieldLeaf
  masterDeveloperCompleteRightsMap : SpringfieldLeaf
  blackRockMirvacAggregateExposure : SpringfieldLeaf
  blackRockMirvacFundVotingDecomposition : SpringfieldLeaf
  publicInfrastructureMixedIncidence : SpringfieldLeaf
  parcelSpecificInfrastructureIncidence : SpringfieldLeaf
  ecologicalCarrierRouting : SpringfieldLeaf
  sameParcelValueEcologyJoin : SpringfieldLeaf

record ClosureReceipt : Set where
  constructor closure-receipt
  field
    leaf : SpringfieldLeaf
    level : ClosureLevel
    closedAtLevel : Bool
    reading : String
open ClosureReceipt public

canonicalClosureReceipts : List ClosureReceipt
canonicalClosureReceipts =
  closure-receipt cityWestAcquisitionVehicle identityLevel true
    "ABR identifies the Gordon Springfield West Unit Trust / Springfield BJM Landlord Trust partnership; legal vehicle identity is paid."
  ∷ closure-receipt cityWestCapitalStack beneficialOwnershipLevel false
    "Lender, secured party, unit-holder split, guarantees and development facility remain open."
  ∷ closure-receipt springfieldGasNetworkLineage networkLevel true
    "The network-level chronology is strongly paid: 2004 Energex/Springfield gas-electric alliance; 2005 Queensland parliamentary same-object statement that Energex through Allgas planned to extend the natural-gas network to Springfield; 2006 Energex Allgas sale to APT/APA; later GDI ownership; 2026 Stonepeak/AGIG."
  ∷ closure-receipt springfieldExactGasAssets instrumentLevel false
    "Exact Springfield easements, mains/service IDs and asset/sale schedules remain open even though the Springfield-to-Allgas network identity is now paid."
  ∷ closure-receipt santoroSpringfieldSubject subjectCategoryLevel true
    "Repeated 2025 Springfield/Santoro access is paid. Public diaries now identify a Springfield City Group Plan update, a project update in the Treasurer/Energy/Home Ownership portfolio and a specific discussion of TAFE premises in Springfield."
  ∷ closure-receipt santoroSpecificAskDecision instrumentLevel false
    "At least one concrete lobbying subject is now identified, but briefing papers, correspondence, requested decisions, outcomes and any gas/energy-specific asks remain open."
  ∷ closure-receipt mirvacOrionChronology transactionLevel true
    "Mirvac pays August 2002 acquisition/agreement chronology, 100% Orion ownership, longitudinal Orion/Orion-land asset entries, development and current asset valuation/land coordinates."
  ∷ closure-receipt mirvacOriginalInstrument instrumentLevel false
    "Original 2002 contract, price, Springfield-side counterparty rights and revenue-sharing/covenants remain open."
  ∷ closure-receipt masterDeveloperParcelActivity transactionLevel true
    "City West sale and Vantage marketing establish continuing parcel allocation/monetisation by Springfield City Group."
  ∷ closure-receipt masterDeveloperCompleteRightsMap parcelIncidenceLevel false
    "Complete retained/sold/optioned/JV/reversionary-rights map remains open."
  ∷ closure-receipt blackRockMirvacAggregateExposure transactionLevel true
    "BlackRock Group aggregate Mirvac substantial holding is paid at 6.66% in 2025 and about 7.70% in 2026."
  ∷ closure-receipt blackRockMirvacFundVotingDecomposition beneficialOwnershipLevel false
    "Underlying funds, mandates, lending/derivative positions and voting instructions remain open."
  ∷ closure-receipt publicInfrastructureMixedIncidence networkLevel true
    "Major public rail/road contributions plus capped developer-charge mechanisms establish mixed public/private growth-infrastructure incidence."
  ∷ closure-receipt parcelSpecificInfrastructureIncidence parcelIncidenceLevel false
    "Parcel-specific charges, offsets/refunds, public works and resulting value uplift remain open."
  ∷ closure-receipt ecologicalCarrierRouting identityLevel true
    "Exact Council/EPBC environmental carrier identities and acquisition routes are paid."
  ∷ closure-receipt sameParcelValueEcologyJoin parcelIncidenceLevel false
    "A same-cadastral-object table joining private value capture to clearing/offset/heat/water/traffic/connectivity burden remains open."
  ∷ []

record ClosureSummary : Set where
  constructor closure-summary
  field
    identityAndChronologySubstantiallyClosed : Bool
    networkOwnershipChronologySubstantiallyClosed : Bool
    lobbyingSubjectCategoriesSubstantiallyClosed : Bool
    beneficialCapitalStackClosed : Bool
    lobbyingCausationClosed : Bool
    parcelIncidenceClosed : Bool
    exactAssetSchedulesClosed : Bool
    nextCutRemainsSameObjectForensic : Bool
open ClosureSummary public

canonicalClosureSummary : ClosureSummary
canonicalClosureSummary = closure-summary
  true true true false false false false true

------------------------------------------------------------------------
-- Remaining Pareto is narrower: documents and joins, not broad web discovery.
------------------------------------------------------------------------

data ClosureDebt : Set where
  cityWestFinanceDocuments : ClosureDebt
  gasAssetSchedules : ClosureDebt
  lobbyingBriefsCorrespondence : ClosureDebt
  orion2002ContractTitle : ClosureDebt
  currentSpringfieldRightsCadastre : ClosureDebt
  blackRockVotingFundLookthrough : ClosureDebt
  parcelInfrastructureLedger : ClosureDebt
  parcelValueEcologyLedger : ClosureDebt

record ClosureCut : Set where
  constructor closure-cut
  field
    debt : ClosureDebt
    priority : Nat
    likelyPublicWebClosable : Bool
    requiredObject : String
open ClosureCut public

canonicalClosureCuts : List ClosureCut
canonicalClosureCuts =
  closure-cut cityWestFinanceDocuments 100 false
    "Title/mortgage/PPSR/company trust or lender disclosures identifying secured finance and beneficial/economic split."
  ∷ closure-cut gasAssetSchedules 100 false
    "Original Energex-Springfield alliance plus exact mains/easement/asset and 2006 sale schedules. The Springfield-to-Allgas network identity itself is now paid."
  ∷ closure-cut lobbyingBriefsCorrespondence 99 false
    "Lobbyist contact-log details plus briefing papers, correspondence, notes, asks and decision traces for 2025 Springfield/Santoro meetings. Public diary subject categories are now substantially paid."
  ∷ closure-cut orion2002ContractTitle 98 false
    "August 2002 Mirvac/Springfield sale-development instrument and historical title/covenant material."
  ∷ closure-cut currentSpringfieldRightsCadastre 98 false
    "Current cadastral ownership/options/JV/reversionary-rights map across Springfield City Group and downstream partners."
  ∷ closure-cut blackRockVotingFundLookthrough 97 true
    "Substantial-holder notice annexures and fund/mandate disclosures decomposing BlackRock's aggregate Mirvac position and voting authority."
  ∷ closure-cut parcelInfrastructureLedger 96 true
    "Infrastructure Charges Notices/register entries plus public works/funding joined to exact development parcels."
  ∷ closure-cut parcelValueEcologyLedger 95 false
    "Title/transaction/development-value data spatially joined to exact Woogaroo/Springview ecological-impact geometry."
  ∷ []
