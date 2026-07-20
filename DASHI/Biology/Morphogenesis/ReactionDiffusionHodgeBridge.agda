module DASHI.Biology.Morphogenesis.ReactionDiffusionHodgeBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Analysis.FiniteOperatorReductionCore as FOR
import DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection as RDM

------------------------------------------------------------------------
-- A finite reaction–diffusion linearisation is a reaction block plus a spatial
-- differential block.  After removal/control of constant modes, its spatial
-- estimate has the same Hodge–Poincaré form already used in the finite YM lane:
-- norm <= differential energy + constraint energy + mean energy.
--
-- This is not a claim that gauge fields and morphogens have the same mechanism.
-- It is reuse of the same finite coercivity theorem for two different operator
-- instances.
------------------------------------------------------------------------

record ReactionDiffusionHodgeIdentification
  {v s : Level}
  (R : RDM.ReactionDiffusionModeSystem)
  (Vector : Set v)
  (Scalar : Set s)
  (order : FOR.OrderedEnergy Scalar)
  : Set (lsuc (v ⊔ s)) where
  field
    hodge :
      FOR.GaugeFixedBlockHodgePoincare Vector Scalar order

    encodeMode :
      RDM.ReactionDiffusionModeSystem.Mode R → Vector

    linearizedModeEnergy :
      RDM.ReactionDiffusionModeSystem.Mode R → Scalar

    linearizedEnergyMatchesHodge :
      (mode : RDM.ReactionDiffusionModeSystem.Mode R) →
      linearizedModeEnergy mode ≡
      FOR.hodgeWeightedEnergy hodge (encodeMode mode)

open ReactionDiffusionHodgeIdentification public

reactionDiffusionModeNormControlled :
  ∀ {v s}
    {R : RDM.ReactionDiffusionModeSystem}
    {Vector : Set v}
    {Scalar : Set s}
    {order : FOR.OrderedEnergy Scalar} →
  (B : ReactionDiffusionHodgeIdentification R Vector Scalar order) →
  (mode : RDM.ReactionDiffusionModeSystem.Mode R) →
  FOR.orderedEnergyLeq order
    (FOR.hodgeNormSquared (hodge B) (encodeMode B mode))
    (linearizedModeEnergy B mode)
reactionDiffusionModeNormControlled B mode
  rewrite linearizedEnergyMatchesHodge B mode =
  FOR.hodgeControlsNorm (hodge B) (encodeMode B mode)

reactionDiffusionZeroBackgroundCoercivity :
  ∀ {v s}
    {R : RDM.ReactionDiffusionModeSystem}
    {Vector : Set v}
    {Scalar : Set s}
    {order : FOR.OrderedEnergy Scalar} →
  (B : ReactionDiffusionHodgeIdentification R Vector Scalar order) →
  (hessianEnergy : Vector → Scalar) →
  ((vector : Vector) →
    hessianEnergy vector ≡ FOR.hodgeWeightedEnergy (hodge B) vector) →
  FOR.ZeroBackgroundCoercivity Vector Scalar order
reactionDiffusionZeroBackgroundCoercivity {order = order} B =
  FOR.hodgePoincareGivesZeroBackgroundCoercivity order (hodge B)

record HodgeControlledTuringSelection
  {v s : Level}
  {R : RDM.ReactionDiffusionModeSystem}
  {Vector : Set v}
  {Scalar : Set s}
  {order : FOR.OrderedEnergy Scalar}
  (B : ReactionDiffusionHodgeIdentification R Vector Scalar order)
  : Set (lsuc (v ⊔ s)) where
  field
    selection :
      RDM.TuringModeSelectionWitness R

    selectedModeNormControlled :
      FOR.orderedEnergyLeq order
        (FOR.hodgeNormSquared (hodge B)
          (encodeMode B
            (RDM.TuringModeSelectionWitness.mode selection)))
        (linearizedModeEnergy B
          (RDM.TuringModeSelectionWitness.mode selection))

open HodgeControlledTuringSelection public

controlSelectedTuringMode :
  ∀ {v s}
    {R : RDM.ReactionDiffusionModeSystem}
    {Vector : Set v}
    {Scalar : Set s}
    {order : FOR.OrderedEnergy Scalar} →
  (B : ReactionDiffusionHodgeIdentification R Vector Scalar order) →
  (selection : RDM.TuringModeSelectionWitness R) →
  HodgeControlledTuringSelection B
controlSelectedTuringMode B selection = record
  { selection = selection
  ; selectedModeNormControlled =
      reactionDiffusionModeNormControlled B
        (RDM.TuringModeSelectionWitness.mode selection)
  }
