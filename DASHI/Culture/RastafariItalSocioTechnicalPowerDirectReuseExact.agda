module DASHI.Culture.RastafariItalSocioTechnicalPowerDirectReuseExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.RastafariItalLoopControlGovernanceExact as Loop
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Socio

------------------------------------------------------------------------
-- DIRECT REUSE OF MERGED SOCIO-TECHNICAL POWER ASSAYS
--
-- PR #662 is canonical on master.  Its finite assays already establish several
-- theorem patterns needed by the Ital return-loop governance lane.  This owner
-- reuses those exact results instead of reproducing them with circular-system
-- names.
--
-- The historical/genre fixtures in the source owner remain calibration cases.
-- Nothing here asserts a historical proposition about Rastafari practice.
------------------------------------------------------------------------

sameFunctionalServiceStillCannotRecoverPowerTopology :
  NonFactor.FactorsThrough Socio.serviceSurface Socio.powerTopology → ⊥
sameFunctionalServiceStillCannotRecoverPowerTopology =
  Socio.serviceCannotRecoverPowerTopology

sameMachineryStillCannotRecoverLabourPower :
  NonFactor.FactorsThrough Socio.machinerySurface Socio.labourPower → ⊥
sameMachineryStillCannotRecoverLabourPower =
  Socio.machineryCannotRecoverLabourPower

labourParticipationStillCannotRecoverPoliticalVoice :
  NonFactor.FactorsThrough Socio.labourParticipation Socio.politicalVoice → ⊥
labourParticipationStillCannotRecoverPoliticalVoice =
  Socio.labourParticipationCannotRecoverPoliticalVoice

broadParticipationStillCannotRecoverMediationControl :
  NonFactor.FactorsThrough Socio.participationSurface Socio.marketMediation → ⊥
broadParticipationStillCannotRecoverMediationControl =
  Socio.participationCannotRecoverMediation

samePlanStillCannotRecoverEcologicalAdmissibility :
  NonFactor.FactorsThrough Socio.industrialPlan Socio.ecologicalAdmissibility → ⊥
samePlanStillCannotRecoverEcologicalAdmissibility =
  Socio.industrialPlanCannotRecoverEcologicalAdmissibility

marketLabelStillCannotRecoverMaterialExitCone :
  NonFactor.FactorsThrough Socio.marketEconomyLabel Socio.materialExitCone → ⊥
marketLabelStillCannotRecoverMaterialExitCone =
  Socio.marketLabelCannotRecoverExitCone

------------------------------------------------------------------------
-- The local Ital specialization remains stronger on loop-specific coordinates:
-- contribution does not recover title, destination control, decision rights,
-- benefit position, provenance custody or institutional power.
------------------------------------------------------------------------

localParticipationStillCannotRecoverDecisionRights :
  NonFactor.FactorsThrough Loop.contribution Loop.decision → ⊥
localParticipationStillCannotRecoverDecisionRights =
  Loop.participationCannotRecoverDecisionRights

localParticipationStillCannotRecoverInstitutionalPower :
  NonFactor.FactorsThrough Loop.contribution Loop.institutionalPower → ⊥
localParticipationStillCannotRecoverInstitutionalPower =
  Loop.participationCannotRecoverInstitutionalPower

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

data CircularTechnologyDeterminesGovernance : Set where

data EcologicalServiceDeterminesPowerTopology : Set where

data ParticipationCountDeterminesControlDistribution : Set where

data CircularInfrastructureDeterminesLabourRelation : Set where

circularTechnologyDoesNotDetermineGovernance :
  CircularTechnologyDeterminesGovernance → ⊥
circularTechnologyDoesNotDetermineGovernance ()

ecologicalServiceDoesNotDeterminePowerTopology :
  EcologicalServiceDeterminesPowerTopology → ⊥
ecologicalServiceDoesNotDeterminePowerTopology ()

participationCountDoesNotDetermineControlDistribution :
  ParticipationCountDeterminesControlDistribution → ⊥
participationCountDoesNotDetermineControlDistribution ()

circularInfrastructureDoesNotDetermineLabourRelation :
  CircularInfrastructureDeterminesLabourRelation → ⊥
circularInfrastructureDoesNotDetermineLabourRelation ()

record ItalSocioTechnicalPowerReuseBoundary : Set where
  constructor italSocioTechnicalPowerReuseBoundary
  field
    sameServiceMeansSamePowerTopology : Bool
    sameServiceMeansSamePowerTopologyIsFalse :
      sameServiceMeansSamePowerTopology ≡ false

    labourParticipationMeansPoliticalVoice : Bool
    labourParticipationMeansPoliticalVoiceIsFalse :
      labourParticipationMeansPoliticalVoice ≡ false

    broadParticipationMeansDistributedControl : Bool
    broadParticipationMeansDistributedControlIsFalse :
      broadParticipationMeansDistributedControl ≡ false

    socioTechnicalOwnerReusedWithoutHistoricalPromotion : Bool
    socioTechnicalOwnerReusedWithoutHistoricalPromotionIsTrue :
      socioTechnicalOwnerReusedWithoutHistoricalPromotion ≡ true

canonicalItalSocioTechnicalPowerReuseBoundary :
  ItalSocioTechnicalPowerReuseBoundary
canonicalItalSocioTechnicalPowerReuseBoundary =
  italSocioTechnicalPowerReuseBoundary
    false refl
    false refl
    false refl
    true refl
