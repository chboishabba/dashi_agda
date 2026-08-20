module DASHI.Core.ActiveInformationDualEffectBridgeExact where

------------------------------------------------------------------------
-- ACTIVE INFORMATION <-> DUAL-EFFECT ACTION BRIDGE
--
-- Reuses the upstream IdentifiabilityActiveInformationExact theorem owner.
-- A declared action acting on the information coordinate becomes an experiment;
-- a DualEffect InformationSeparatingAction is therefore exactly a
-- DistinguishingExperiment on that induced experiment system.
------------------------------------------------------------------------

open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.DualEffectInformationActionExact as Dual
import DASHI.Core.IdentifiabilityActiveInformationExact as Active

informationActionExperimentSystem :
  ∀ {World Information Action Observation} →
  Dual.DualEffectAction World Information Action →
  (Information → Observation) →
  Active.ExperimentSystem Information Action Observation
informationActionExperimentSystem system observe =
  Active.experimentSystem
    (λ action information →
      observe (Dual.informationStep system action information))

separatingActionIsDistinguishingExperiment :
  ∀ {World Information Action Observation}
    {system : Dual.DualEffectAction World Information Action}
    {observe : Information → Observation}
    {action : Action}
    {left right : Information} →
  Dual.InformationSeparatingAction system observe action left right →
  Active.DistinguishingExperiment
    (informationActionExperimentSystem system observe)
    left right
separatingActionIsDistinguishingExperiment witness =
  Active.distinguishingExperiment
    _
    (Dual.InformationSeparatingAction.differAfter witness)

------------------------------------------------------------------------
-- This bridge does not construct action value/cost, welfare permission or an
-- authority to execute the experiment.  It only identifies the exact
-- separation theorem shared by the two interfaces.
------------------------------------------------------------------------
