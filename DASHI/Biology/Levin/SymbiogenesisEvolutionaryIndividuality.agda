module DASHI.Biology.Levin.SymbiogenesisEvolutionaryIndividuality where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.EndosymbioticOrganelleAgencyBoundary as Organelle
import DASHI.Biology.Levin.MultikingdomEmbodiedAgentCore as Multikingdom
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy

record EvolutionaryIndividualityWitness : Set where
  field
    componentVariationSpecified : Bool
    collectiveVariationSpecified : Bool
    componentFitnessMeasured : Bool
    collectiveFitnessMeasured : Bool
    reproductiveCouplingMeasured : Bool
    inheritanceCouplingMeasured : Bool
    conflictMediationMeasured : Bool
    divisionOfLabourMeasured : Bool
    dependencyMeasured : Bool
    perturbationRecoveryMeasured : Bool
    multigenerationalPersistenceMeasured : Bool

record EvolutionaryIndividualityPromotionGate : Set where
  field
    organelleBoundary : Organelle.EndosymbioticOrganelleAgencyBoundary
    multikingdomCore : Multikingdom.MultikingdomEmbodiedAgentCore
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    cooperationNotIndividualityByDefinition : Bool
    physicalAssociationNotReproductiveUnity : Bool
    highRelatednessNotSufficientByItself : Bool
    conflictSuppressionRequired : Bool
    collectiveInheritanceRequired : Bool
    fitnessAlignmentRequiresMeasurement : Bool
    newHigherLevelIndividualAdmissible : Bool
    promotionAllowedWithoutWitness : Bool
    interpretation : String

canonicalEvolutionaryIndividualityPromotionGate : EvolutionaryIndividualityPromotionGate
canonicalEvolutionaryIndividualityPromotionGate = record
  { organelleBoundary = Organelle.canonicalEndosymbioticOrganelleAgencyBoundary
  ; multikingdomCore = Multikingdom.canonicalMultikingdomEmbodiedAgentCore
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; cooperationNotIndividualityByDefinition = true
  ; physicalAssociationNotReproductiveUnity = true
  ; highRelatednessNotSufficientByItself = true
  ; conflictSuppressionRequired = true
  ; collectiveInheritanceRequired = true
  ; fitnessAlignmentRequiresMeasurement = true
  ; newHigherLevelIndividualAdmissible = true
  ; promotionAllowedWithoutWitness = false
  ; interpretation = "Symbiogenesis may produce a new evolutionary individual when formerly separable components acquire reproductive and inheritance coupling, conflict mediation, dependency, division of labour and measurable collective fitness; association or cooperation alone does not cross that boundary"
  }
