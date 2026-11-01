module DASHI.Governance.AUKUSPacificStrategicDependenceSafetyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Foundations.CabarlahGoniometerAcquisitionExact as Cabarlah
import DASHI.Law.AustraliaMilitaryMarathonSecuritySourceReceiptsExact as Military

------------------------------------------------------------------------
-- AUKUS / PACIFIC STRATEGIC DEPENDENCE / SUBMARINE SAFETY
------------------------------------------------------------------------

aukusReuters2026 : Source.AttributedSource
aukusReuters2026 = Source.mkNoDOISource
  "Reuters"
  "Australia's Albanese says AUKUS remains 'full steam ahead' after Trump call"
  "Reuters"
  "2026-08-13"
  "https://www.reuters.com/world/asia-pacific/australias-albanese-says-aukus-remains-full-steam-ahead-after-trump-call-2026-08-13/"
  Source.newsSource
  "current secondary source for Australian government commitment to AUKUS, planned U.S. submarine rotations, future Virginia-class purchases and strategic framing around China"
  Source.publicAttribution

ehimeNTSB : Source.AttributedSource
ehimeNTSB = Source.mkNoDOISource
  "National Transportation Safety Board"
  "Collision between the U.S. Navy Submarine USS Greeneville and Japanese Motor Vessel Ehime Maru"
  "Marine Accident Investigation DCA01MM022"
  "2001 / report 2005"
  "https://www.ntsb.gov/investigations/Pages/DCA01MM022.aspx"
  Source.governmentSource
  "official accident source: USS Greeneville emergency surfacing struck and sank Ehime Maru off Oahu; bounded historical safety precedent only"
  Source.publicAttribution

irisDenaReuters2026 : Source.AttributedSource
irisDenaReuters2026 = Source.mkNoDOISource
  "Reuters"
  "Three Australians were aboard US submarine that sank Iranian ship, PM Albanese says"
  "Reuters"
  "2026-03-06"
  "https://www.reuters.com/world/asia-pacific/three-australians-were-aboard-us-submarine-that-sunk-iranian-ship-pm-albanese-2026-03-06/"
  Source.newsSource
  "secondary report confirming three Australian defence personnel aboard the U.S. submarine that sank IRIS Dena off Sri Lanka; Albanese stated they did not participate in the attack"
  Source.publicAttribution

data StrategicDependenceAxis : Set where
  submarineIndustrialCapacity : StrategicDependenceAxis
  usOperationalAccess : StrategicDependenceAxis
  australianCommandSovereignty : StrategicDependenceAxis
  nuclearStewardship : StrategicDependenceAxis
  pacificRegionalLegitimacy : StrategicDependenceAxis
  sensingInfrastructure : StrategicDependenceAxis
  historicalSubmarineSafety : StrategicDependenceAxis
  alliedCombatPresence : StrategicDependenceAxis

record StrategicDependenceObservation : Set where
  constructor strategic-dependence-observation
  field
    axis : StrategicDependenceAxis
    reading : String
    source : Source.AttributedSource
    provesAUKUSFailure : Bool
    provesAUKUSSuccess : Bool
    provesLossOfAustralianSovereignty : Bool

open StrategicDependenceObservation public

officialAUKUSCommitment : StrategicDependenceObservation
officialAUKUSCommitment = strategic-dependence-observation
  usOperationalAccess
  "The Australian government publicly describes AUKUS as proceeding and plans rotational U.S. submarine presence from 2027."
  aukusReuters2026
  false false false

historicalSubmarineSafetyCase : StrategicDependenceObservation
historicalSubmarineSafetyCase = strategic-dependence-observation
  historicalSubmarineSafety
  "The Greeneville/Ehime Maru accident is retained as a historical navigation/procedure safety case only."
  ehimeNTSB
  false false false

irisDenaPresenceCase : StrategicDependenceObservation
irisDenaPresenceCase = strategic-dependence-observation
  alliedCombatPresence
  "Three Australian personnel were aboard a U.S. submarine during the strike that sank IRIS Dena off Sri Lanka; the Australian government states they did not participate in offensive action."
  irisDenaReuters2026
  false false false

iranWarshipCorrectionRetained : Military.ContemporarySourceReceipt
iranWarshipCorrectionRetained = Military.warshipCorrectionReceipt

australianPresenceReceiptRetained : Military.ContemporarySourceReceipt
australianPresenceReceiptRetained = Military.threeAustraliansReceipt

nonParticipationReceiptRetained : Military.ContemporarySourceReceipt
nonParticipationReceiptRetained = Military.nonParticipationGovernmentReceipt

cabarlahBoundary : Cabarlah.CabarlahGoniometerBoundary
cabarlahBoundary = Cabarlah.canonicalCabarlahGoniometerBoundary

data HistoricalAccidentPredictsAUKUSAccident : Set where
data HistoricalDirectionFindingProvesCurrentAUKUSSurveillance : Set where
data SensingCapabilityCreatesTargetingAuthority : Set where
data AllianceAccessEqualsCommandTransfer : Set where
data PresenceAboardCombatPlatformProvesParticipation : Set where
data GovernmentNonParticipationStatementEqualsIndependentActionReconstruction : Set where
data AlliedCombatPresenceAutomaticallyProvesLossOfSovereignty : Set where

historicalAccidentDoesNotPredictAUKUSAccident :
  HistoricalAccidentPredictsAUKUSAccident → ⊥
historicalAccidentDoesNotPredictAUKUSAccident ()

cabarlahLineageDoesNotProveCurrentAUKUSDeployment :
  HistoricalDirectionFindingProvesCurrentAUKUSSurveillance → ⊥
cabarlahLineageDoesNotProveCurrentAUKUSDeployment ()

sensingCapabilityDoesNotCreateTargetingAuthority :
  SensingCapabilityCreatesTargetingAuthority → ⊥
sensingCapabilityDoesNotCreateTargetingAuthority ()

allianceAccessDoesNotDefinitionallyEqualCommandTransfer :
  AllianceAccessEqualsCommandTransfer → ⊥
allianceAccessDoesNotDefinitionallyEqualCommandTransfer ()

presenceAboardCombatPlatformDoesNotProveParticipation :
  PresenceAboardCombatPlatformProvesParticipation → ⊥
presenceAboardCombatPlatformDoesNotProveParticipation ()

governmentStatementDoesNotEqualIndependentActionReconstruction :
  GovernmentNonParticipationStatementEqualsIndependentActionReconstruction → ⊥
governmentStatementDoesNotEqualIndependentActionReconstruction ()

combatPresenceDoesNotByItselfProveSovereigntyLoss :
  AlliedCombatPresenceAutomaticallyProvesLossOfSovereignty → ⊥
combatPresenceDoesNotByItselfProveSovereigntyLoss ()
