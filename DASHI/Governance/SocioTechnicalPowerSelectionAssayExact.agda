module DASHI.Governance.SocioTechnicalPowerSelectionAssayExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.HistoryQualifiedSelectionTopologyExact as Selection
import DASHI.Governance.OptionConeCoercionExact as OptionCone
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition

------------------------------------------------------------------------
-- SOCIO-TECHNICAL POWER / SELECTION ASSAYS
--
-- Genre and historical labels are deliberately coarse observer surfaces.  The
-- finite states below are synthetic DASHI countermodels used to test whether a
-- consumer silently collapses technology, ownership, labour, maintenance,
-- ecological fit, social provision, political voice or market mediation.
--
-- Solarpunk/cyberpunk/steampunk, Luddite/textile, suffrage, company-town,
-- Ford-Amazon-rubber, plantation/export-enclave and retail/institutional-market
-- examples are calibration domains only.  No historical proposition is proved
-- by these finite constructors, and no genre is assigned a necessary politics.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Same functional service surface, different power topology.
------------------------------------------------------------------------

data ServiceState : Set where
  concentratedService distributedService : ServiceState

data ServiceSurface : Set where
  sameEnergyMobilityCommunication : ServiceSurface

data PowerTopology : Set where
  concentratedPower distributedPower : PowerTopology

serviceSurface : ServiceState → ServiceSurface
serviceSurface _ = sameEnergyMobilityCommunication

powerTopology : ServiceState → PowerTopology
powerTopology concentratedService = concentratedPower
powerTopology distributedService = distributedPower

sameServiceProjection :
  serviceSurface concentratedService ≡ serviceSurface distributedService
sameServiceProjection = refl

powerTopologyDiffers :
  powerTopology concentratedService ≡ powerTopology distributedService → ⊥
powerTopologyDiffers ()

serviceCannotRecoverPowerTopology :
  INF.FactorsThrough serviceSurface powerTopology → ⊥
serviceCannotRecoverPowerTopology =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      concentratedService
      distributedService
      sameServiceProjection
      powerTopologyDiffers)

------------------------------------------------------------------------
-- Genre observer labels do not determine fine political-economic structure.
------------------------------------------------------------------------

data GenreState : Set where
  solarCommons solarCentralised cyberCorporate cyberCommons : GenreState

data GenreLabel : Set where
  solarpunk cyberpunk : GenreLabel

data GovernanceForm : Set where
  commonsGovernance centralisedGovernance corporateGovernance : GovernanceForm

genreLabel : GenreState → GenreLabel
genreLabel solarCommons = solarpunk
genreLabel solarCentralised = solarpunk
genreLabel cyberCorporate = cyberpunk
genreLabel cyberCommons = cyberpunk

governanceForm : GenreState → GovernanceForm
governanceForm solarCommons = commonsGovernance
governanceForm solarCentralised = centralisedGovernance
governanceForm cyberCorporate = corporateGovernance
governanceForm cyberCommons = commonsGovernance

sameSolarLabel : genreLabel solarCommons ≡ genreLabel solarCentralised
sameSolarLabel = refl

solarGovernanceDiffers :
  governanceForm solarCommons ≡ governanceForm solarCentralised → ⊥
solarGovernanceDiffers ()

solarpunkLabelCannotRecoverGovernance :
  INF.FactorsThrough genreLabel governanceForm → ⊥
solarpunkLabelCannotRecoverGovernance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      solarCommons
      solarCentralised
      sameSolarLabel
      solarGovernanceDiffers)

------------------------------------------------------------------------
-- Mechanisation does not determine labour relation / surplus routing.
------------------------------------------------------------------------

data MechanisedState : Set where
  workerSharedGain ownerConcentratedGain : MechanisedState

data MachinerySurface : Set where
  sameMechanisedProduction : MachinerySurface

data LabourPower : Set where
  bargainingExpanded bargainingContracted : LabourPower

data SurplusRoute : Set where
  sharedSurplus concentratedSurplus : SurplusRoute

machinerySurface : MechanisedState → MachinerySurface
machinerySurface _ = sameMechanisedProduction

labourPower : MechanisedState → LabourPower
labourPower workerSharedGain = bargainingExpanded
labourPower ownerConcentratedGain = bargainingContracted

surplusRoute : MechanisedState → SurplusRoute
surplusRoute workerSharedGain = sharedSurplus
surplusRoute ownerConcentratedGain = concentratedSurplus

sameMachinery :
  machinerySurface workerSharedGain ≡ machinerySurface ownerConcentratedGain
sameMachinery = refl

labourPowerDiffers :
  labourPower workerSharedGain ≡ labourPower ownerConcentratedGain → ⊥
labourPowerDiffers ()

machineryCannotRecoverLabourPower :
  INF.FactorsThrough machinerySurface labourPower → ⊥
machineryCannotRecoverLabourPower =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      workerSharedGain
      ownerConcentratedGain
      sameMachinery
      labourPowerDiffers)

------------------------------------------------------------------------
-- Labour participation and political voice are orthogonal coordinates.
------------------------------------------------------------------------

data LabourPoliticalState : Set where
  industrialWorkerDisenfranchised industrialWorkerEnfranchised : LabourPoliticalState

data LabourParticipation : Set where
  participatesInProduction : LabourParticipation

data PoliticalVoice : Set where
  franchiseAbsent franchisePresent : PoliticalVoice

labourParticipation : LabourPoliticalState → LabourParticipation
labourParticipation _ = participatesInProduction

politicalVoice : LabourPoliticalState → PoliticalVoice
politicalVoice industrialWorkerDisenfranchised = franchiseAbsent
politicalVoice industrialWorkerEnfranchised = franchisePresent

sameLabourParticipation :
  labourParticipation industrialWorkerDisenfranchised
  ≡ labourParticipation industrialWorkerEnfranchised
sameLabourParticipation = refl

politicalVoiceDiffers :
  politicalVoice industrialWorkerDisenfranchised
  ≡ politicalVoice industrialWorkerEnfranchised → ⊥
politicalVoiceDiffers ()

labourParticipationCannotRecoverPoliticalVoice :
  INF.FactorsThrough labourParticipation politicalVoice → ⊥
labourParticipationCannotRecoverPoliticalVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      industrialWorkerDisenfranchised
      industrialWorkerEnfranchised
      sameLabourParticipation
      politicalVoiceDiffers)

------------------------------------------------------------------------
-- Transporting an industrial plan does not transport ecological admissibility.
-- This is the synthetic assay used for Ford-rubber-style locality failures.
------------------------------------------------------------------------

data TransplantedPlanState : Set where
  locallyCompatible ecologyMismatch : TransplantedPlanState

data IndustrialPlan : Set where
  samePlantationPlan : IndustrialPlan

data EcologicalAdmissibility : Set where
  ecologyAdmitted ecologyBlocked : EcologicalAdmissibility

industrialPlan : TransplantedPlanState → IndustrialPlan
industrialPlan _ = samePlantationPlan

ecologicalAdmissibility : TransplantedPlanState → EcologicalAdmissibility
ecologicalAdmissibility locallyCompatible = ecologyAdmitted
ecologicalAdmissibility ecologyMismatch = ecologyBlocked

sameIndustrialPlan :
  industrialPlan locallyCompatible ≡ industrialPlan ecologyMismatch
sameIndustrialPlan = refl

ecologicalAdmissibilityDiffers :
  ecologicalAdmissibility locallyCompatible
  ≡ ecologicalAdmissibility ecologyMismatch → ⊥
ecologicalAdmissibilityDiffers ()

industrialPlanCannotRecoverEcologicalAdmissibility :
  INF.FactorsThrough industrialPlan ecologicalAdmissibility → ⊥
industrialPlanCannotRecoverEcologicalAdmissibility =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      locallyCompatible
      ecologyMismatch
      sameIndustrialPlan
      ecologicalAdmissibilityDiffers)

------------------------------------------------------------------------
-- Same market-participation surface, different mediation/control topology.
-- Useful for retail order origin vs broker/wholesaler/exchange infrastructure.
------------------------------------------------------------------------

data MarketState : Set where
  broadRetailConcentratedRouting broadRetailDistributedRouting : MarketState

data ParticipationSurface : Set where
  broadParticipation : ParticipationSurface

data MarketMediation : Set where
  concentratedMediation distributedMediation : MarketMediation

participationSurface : MarketState → ParticipationSurface
participationSurface _ = broadParticipation

marketMediation : MarketState → MarketMediation
marketMediation broadRetailConcentratedRouting = concentratedMediation
marketMediation broadRetailDistributedRouting = distributedMediation

sameParticipation :
  participationSurface broadRetailConcentratedRouting
  ≡ participationSurface broadRetailDistributedRouting
sameParticipation = refl

mediationDiffers :
  marketMediation broadRetailConcentratedRouting
  ≡ marketMediation broadRetailDistributedRouting → ⊥
mediationDiffers ()

participationCannotRecoverMediation :
  INF.FactorsThrough participationSurface marketMediation → ⊥
participationCannotRecoverMediation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      broadRetailConcentratedRouting
      broadRetailDistributedRouting
      sameParticipation
      mediationDiffers)

------------------------------------------------------------------------
-- Same coarse market-economy label, different material exit geometry.
------------------------------------------------------------------------

data MarketEconomyState : Set where
  lowSocialFloor highSocialFloor : MarketEconomyState

data MarketEconomyLabel : Set where
  marketEconomy : MarketEconomyLabel

data MaterialExitCone : Set where
  narrowExitCone widerExitCone : MaterialExitCone

marketEconomyLabel : MarketEconomyState → MarketEconomyLabel
marketEconomyLabel _ = marketEconomy

materialExitCone : MarketEconomyState → MaterialExitCone
materialExitCone lowSocialFloor = narrowExitCone
materialExitCone highSocialFloor = widerExitCone

sameMarketLabel :
  marketEconomyLabel lowSocialFloor ≡ marketEconomyLabel highSocialFloor
sameMarketLabel = refl

exitConeDiffers :
  materialExitCone lowSocialFloor ≡ materialExitCone highSocialFloor → ⊥
exitConeDiffers ()

marketLabelCannotRecoverExitCone :
  INF.FactorsThrough marketEconomyLabel materialExitCone → ⊥
marketLabelCannotRecoverExitCone =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      lowSocialFloor
      highSocialFloor
      sameMarketLabel
      exitConeDiffers)

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

selectionTopologyBoundary : Selection.HistoryQualifiedSelectionBoundary
selectionTopologyBoundary = Selection.canonicalHistoryQualifiedSelectionBoundary

antiDomesticationBoundary : Opposition.OppositionInterfaceAntiDomesticationBoundary
antiDomesticationBoundary =
  Opposition.canonicalOppositionInterfaceAntiDomesticationBoundary

canonicalOptionConeContraction :
  OptionCone.StrictSafeReachabilityContraction
    OptionCone.demoReachability
    OptionCone.beforeResponse
    OptionCone.coerciveOutcome
canonicalOptionConeContraction =
  OptionCone.canonicalCoerciveReachabilityContraction

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record SocioTechnicalPowerSelectionBoundary : Set where
  constructor socio-technical-power-selection-boundary
  field
    sameServiceMeansSamePower : Bool
    sameServiceMeansSamePowerIsFalse : sameServiceMeansSamePower ≡ false
    genreLabelDeterminesPolitics : Bool
    genreLabelDeterminesPoliticsIsFalse : genreLabelDeterminesPolitics ≡ false
    sameMachineryMeansSameLabourRelation : Bool
    sameMachineryMeansSameLabourRelationIsFalse :
      sameMachineryMeansSameLabourRelation ≡ false
    labourParticipationImpliesPoliticalVoice : Bool
    labourParticipationImpliesPoliticalVoiceIsFalse :
      labourParticipationImpliesPoliticalVoice ≡ false
    sameIndustrialPlanTransportsEcologicalFit : Bool
    sameIndustrialPlanTransportsEcologicalFitIsFalse :
      sameIndustrialPlanTransportsEcologicalFit ≡ false
    broadParticipationMeansDistributedMediation : Bool
    broadParticipationMeansDistributedMediationIsFalse :
      broadParticipationMeansDistributedMediation ≡ false
    marketEconomyLabelDeterminesExitCone : Bool
    marketEconomyLabelDeterminesExitConeIsFalse :
      marketEconomyLabelDeterminesExitCone ≡ false
    syntheticAssayProvesHistoricalCase : Bool
    syntheticAssayProvesHistoricalCaseIsFalse :
      syntheticAssayProvesHistoricalCase ≡ false

canonicalSocioTechnicalPowerSelectionBoundary :
  SocioTechnicalPowerSelectionBoundary
canonicalSocioTechnicalPowerSelectionBoundary =
  socio-technical-power-selection-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
