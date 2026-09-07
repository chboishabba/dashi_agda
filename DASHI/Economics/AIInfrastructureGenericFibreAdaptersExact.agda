module DASHI.Economics.AIInfrastructureGenericFibreAdaptersExact where

open import DASHI.Core.Prelude

import DASHI.Core.SituatedActionabilityFibreExact as Action
import DASHI.Core.TrajectoryRecoveryFibreExact as Recovery
import DASHI.Core.MultiaxialIncidenceFibreExact as Incidence
import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact as Market
import DASHI.Economics.ClimateAIInfrastructureTransitionRiskCrossPollinationExact as Transition

------------------------------------------------------------------------
-- THIN AI ADAPTERS TO GENERIC FIBRE OWNERS
--
-- AI infrastructure no longer owns the generic theorems.  It supplies domain
-- coordinates and witnesses to Core fibre machinery.
------------------------------------------------------------------------

actionabilityFibre : Action.SituatedActionabilityFibre
actionabilityFibre = Market.infrastructureActionabilityFibre

actionabilityWitness :
  Action.SameSignalDifferentActionability actionabilityFibre
actionabilityWitness = Market.infrastructureSameSignalDifferentActionability

------------------------------------------------------------------------
-- Transition/recovery adapter.
------------------------------------------------------------------------

data CapitalRecoveryStatus : Set where
  capitalRecovered capitalImpaired : CapitalRecoveryStatus

data CapitalFutureCone : Set where
  broadCapitalFuture constrainedCapitalFuture : CapitalFutureCone

capitalRecoveryStatus : Transition.InfrastructureTransitionState → CapitalRecoveryStatus
capitalRecoveryStatus Transition.preBuild = capitalRecovered
capitalRecoveryStatus Transition.capacityBuiltEconomicsIntact = capitalRecovered
capitalRecoveryStatus Transition.capacityBuiltEconomicsImpaired = capitalImpaired
capitalRecoveryStatus Transition.capacityRetrofittedButLegacyLossRetained = capitalImpaired

capitalFuture : Transition.InfrastructureTransitionState → CapitalFutureCone
capitalFuture Transition.preBuild = broadCapitalFuture
capitalFuture Transition.capacityBuiltEconomicsIntact = broadCapitalFuture
capitalFuture Transition.capacityBuiltEconomicsImpaired = constrainedCapitalFuture
capitalFuture Transition.capacityRetrofittedButLegacyLossRetained = constrainedCapitalFuture

capitalResidueFlag : Transition.InfrastructureTransitionState → Residue.ResidueFlag
capitalResidueFlag Transition.preBuild = Residue.residueAbsent
capitalResidueFlag Transition.capacityBuiltEconomicsIntact = Residue.residuePresent
capitalResidueFlag Transition.capacityBuiltEconomicsImpaired = Residue.residuePresent
capitalResidueFlag Transition.capacityRetrofittedButLegacyLossRetained = Residue.residuePresent

transitionRecoveryFibre : Recovery.TrajectoryRecoveryFibre
transitionRecoveryFibre = record
  { State = Transition.InfrastructureTransitionState
  ; CoarseEndpoint = Transition.CoarseCapacityShadow
  ; RecoveryState = CapitalRecoveryStatus
  ; FutureCone = CapitalFutureCone
  ; endpointOf = Transition.capacityShadow
  ; residueOf = capitalResidueFlag
  ; recoveryOf = capitalRecoveryStatus
  ; futureOf = capitalFuture
  ; recoveryReading = "AI infrastructure capital recovery is a fibre over coarse installed-capacity endpoints; retained financing/obsolescence history remains independently observable."
  }

sameCapacityDifferentRecovery :
  Recovery.SameEndpointDifferentRecovery transitionRecoveryFibre
sameCapacityDifferentRecovery = record
  { leftState = Transition.capacityBuiltEconomicsIntact
  ; rightState = Transition.capacityBuiltEconomicsImpaired
  ; sameEndpoint = refl
  ; recoveryDiffers = λ ()
  }

sameCapacityDifferentFuture :
  Recovery.SameEndpointDifferentFuture transitionRecoveryFibre
sameCapacityDifferentFuture = record
  { futureLeft = Transition.capacityBuiltEconomicsIntact
  ; futureRight = Transition.capacityBuiltEconomicsImpaired
  ; futureSameEndpoint = refl
  ; futureDiffers = λ ()
  }

------------------------------------------------------------------------
-- Incidence adapter.  Same technical restoration can have different burden
-- allocation.  The concrete burden semantics remain application-owned.
------------------------------------------------------------------------

data TechnicalRecovery : Set where technicallyRecovered : TechnicalRecovery
data PhenomenonResidual : Set where samePhenomenonResidual : PhenomenonResidual
data EpistemicResidual : Set where sameEpistemicResidual : EpistemicResidual
data PoliticalResidual : Set where lowPoliticalResidual highPoliticalResidual : PoliticalResidual
data ResponsibilityResidual : Set where privateLoss publicLoss : ResponsibilityResidual
data CategoryResidual : Set where sameCategoryResidual : CategoryResidual

data IncidenceState : Set where
  privateAbsorption publicRiskTransfer : IncidenceState

incidenceFibre : Incidence.MultiaxialIncidenceFibre
incidenceFibre = record
  { State = IncidenceState
  ; TechnicalOutcome = TechnicalRecovery
  ; PhenomenonResidual = PhenomenonResidual
  ; EpistemicResidual = EpistemicResidual
  ; PoliticalResidual = PoliticalResidual
  ; ResponsibilityResidual = ResponsibilityResidual
  ; CategoryResidual = CategoryResidual
  ; technicalOutcomeOf = λ _ → technicallyRecovered
  ; phenomenonResidualOf = λ _ → samePhenomenonResidual
  ; epistemicResidualOf = λ _ → sameEpistemicResidual
  ; politicalResidualOf = λ
      { privateAbsorption → lowPoliticalResidual
      ; publicRiskTransfer → highPoliticalResidual
      }
  ; responsibilityResidualOf = λ
      { privateAbsorption → privateLoss
      ; publicRiskTransfer → publicLoss
      }
  ; categoryResidualOf = λ _ → sameCategoryResidual
  ; incidenceReading = "Identical technical recovery can sit over distinct political/responsibility fibres depending on who absorbed transition losses."
  }

sameTechnicalDifferentResponsibility :
  Incidence.SameTechnicalOutcomeDifferentResponsibility incidenceFibre
sameTechnicalDifferentResponsibility = record
  { leftState = privateAbsorption
  ; rightState = publicRiskTransfer
  ; sameTechnicalOutcome = refl
  ; responsibilityDiffers = λ ()
  }

sameTechnicalDifferentPolitics :
  Incidence.SameTechnicalOutcomeDifferentPolitics incidenceFibre
sameTechnicalDifferentPolitics = record
  { politicalLeft = privateAbsorption
  ; politicalRight = publicRiskTransfer
  ; politicalSameTechnicalOutcome = refl
  ; politicalDiffers = λ ()
  }

------------------------------------------------------------------------
-- Domain-boundary firewalls.
------------------------------------------------------------------------

data GenericFibreImpliesAIEmpiricalClaimPermission : Set where

data AIInstantiationMakesTradingClimateAIIdenticalPermission : Set where

genericFibreDoesNotAutoPromoteToAIEmpiricalClaim :
  GenericFibreImpliesAIEmpiricalClaimPermission → ⊥
genericFibreDoesNotAutoPromoteToAIEmpiricalClaim ()

sharedGenericOwnerDoesNotIdentifyApplicationDomains :
  AIInstantiationMakesTradingClimateAIIdenticalPermission → ⊥
sharedGenericOwnerDoesNotIdentifyApplicationDomains ()
