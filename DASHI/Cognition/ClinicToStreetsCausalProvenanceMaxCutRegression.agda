module DASHI.Cognition.ClinicToStreetsCausalProvenanceMaxCutRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Data.Empty using (⊥)

import DASHI.Cognition.ClinicToStreetsCausalProvenanceMaxCutExact as M

structuralEdgeActuallyDeleted :
  M.edgeVisible M.atomisedView M.structuralToFamily ≡ false
structuralEdgeActuallyDeleted = refl

familyEdgeActuallyRetained :
  M.edgeVisible M.atomisedView M.familyToPsychic ≡ true
familyEdgeActuallyRetained = refl

representedUpstreamDrops :
  M.psychicUpstreamSalience M.fullView ≡ 9
  × M.psychicUpstreamSalience M.atomisedView ≡ 3
representedUpstreamDrops = refl , refl

individualResponsibilityCoordinateRises :
  M.ResponsibilityProfile.individualShare M.fullResponsibility ≡ 1
  × M.ResponsibilityProfile.individualShare M.atomisedResponsibility ≡ 7
individualResponsibilityCoordinateRises = refl , refl

actionConeContracts :
  M.actionConeCardinality M.fullView ≡ 3
  × M.actionConeCardinality M.atomisedView ≡ 1
actionConeContracts = refl , refl

reskillingRestoresCone :
  M.actionConeCardinality M.reskilledView ≡ 3
reskillingRestoresCone = refl

weightPromotionFirewall :
  M.ModelWeightImpliesEmpiricalMagnitude → ⊥
weightPromotionFirewall = M.modelWeightDoesNotEstablishEmpiricalMagnitude

faultPromotionFirewall :
  M.ResponsibilityCoordinateImpliesMoralFault → ⊥
faultPromotionFirewall = M.responsibilityCoordinateDoesNotEstablishMoralFault

intentPromotionFirewall :
  M.ActionConeContractionImpliesIntent → ⊥
intentPromotionFirewall = M.actionConeContractionDoesNotEstablishIntent
