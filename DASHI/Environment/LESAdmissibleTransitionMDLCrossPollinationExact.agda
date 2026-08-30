module DASHI.Environment.LESAdmissibleTransitionMDLCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Reaction
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as Soil

------------------------------------------------------------------------
-- LES / SOIL-BIOGEOCHEMISTRY ADAPTER
--
-- SoilBiogeochemistryProcessNetworkExact already records moisture/temperature,
-- kinetic, stoichiometric and scale references for a process.  This adapter does
-- not invent their quantitative laws.  It says that a selected soil process can
-- be given a typed enablement semantics for its existing chemistry transition,
-- after which admissibility and consumer-sensitive MDL can be reasoned about by
-- the generic owners.
------------------------------------------------------------------------

record SoilProcessEnablement
    (process : Soil.SoilCNProcess) : Set₁ where
  constructor soilProcessEnablement
  field
    semantics : Reaction.TypedReactionSemantics
      (Soil.chemistryTransition process)
    soilStateIdentificationReference : String
    processGuardCalibrationReference : String
    validationReference : String

open SoilProcessEnablement public

soilProcessTransitionSystem :
  ∀ {process} →
  SoilProcessEnablement process →
  DASHI.Core.AdmissibleTransitionHyperfabricExact.AdmissibleTransitionSystem
soilProcessTransitionSystem enabled =
  Reaction.reactionTransitionSystem (semantics enabled)

record SoilProcessMDLFamily
    {process : Soil.SoilCNProcess}
    (enabled : SoilProcessEnablement process) : Set₁ where
  constructor soilProcessMDLFamily
  field
    models : Reaction.ReactionEnablementModel (semantics enabled)
    processConsumerReference : String
    codingReference : String

open SoilProcessMDLFamily public

soilProcessMDLProblem :
  ∀ {process}
    {enabled : SoilProcessEnablement process} →
  SoilProcessMDLFamily enabled →
  MDL.ConsumerMDLProblem
soilProcessMDLProblem family =
  Reaction.reactionEnablementMDLProblem (models family)

record LESAdmissibleTransitionMDLBoundary : Set where
  constructor lesAdmissibleTransitionMDLBoundary
  field
    soilProcessNameAloneProvesEnablement : Bool
    soilProcessNameAloneProvesEnablementIsFalse :
      soilProcessNameAloneProvesEnablement ≡ false

    moistureTemperatureReferenceAloneProvesGuard : Bool
    moistureTemperatureReferenceAloneProvesGuardIsFalse :
      moistureTemperatureReferenceAloneProvesGuard ≡ false

    typedEnablementCanFeedGenericTransitionHyperfabric : Bool
    typedEnablementCanFeedGenericTransitionHyperfabricIsTrue :
      typedEnablementCanFeedGenericTransitionHyperfabric ≡ true

    consumerAdequacyConstrainsMDLSelection : Bool
    consumerAdequacyConstrainsMDLSelectionIsTrue :
      consumerAdequacyConstrainsMDLSelection ≡ true

canonicalLESAdmissibleTransitionMDLBoundary :
  LESAdmissibleTransitionMDLBoundary
canonicalLESAdmissibleTransitionMDLBoundary =
  lesAdmissibleTransitionMDLBoundary false refl false refl true refl true refl
