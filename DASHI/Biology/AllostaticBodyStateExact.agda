module DASHI.Biology.AllostaticBodyStateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- MULTISYSTEM ALLOSTATIC BODY CARRIER
--
-- Literature calibration:
-- Bruce S. McEwen,
-- "Stress, Adaptation, and Disease: Allostasis and Allostatic Load",
-- DOI 10.1111/j.1749-6632.1998.tb09546.x.
--
-- Bruce S. McEwen,
-- "Neurobiological and Systemic Effects of Chronic Stress",
-- DOI 10.1177/2470547017692328.
--
-- The pre-existing embodied core carries NE/cortisol/sympathetic/
-- parasympathetic coordinates.  This extension retains that owner while adding
-- dopamine, HPA-regime, metabolic and immune coordinates.  No scalar stress
-- index is promoted to the full body state.
------------------------------------------------------------------------

record AllostaticBodyState : Set where
  constructor allostaticBodyState
  field
    autonomicEndocrineCore : Embodied.BodyState
    dopamine : Embodied.Activation
    hpaRegime : Embodied.Activation
    metabolic : Embodied.Activation
    immune : Embodied.Activation

open AllostaticBodyState public

regulatedExtended : AllostaticBodyState
regulatedExtended =
  allostaticBodyState
    Embodied.regulatedBody
    Embodied.medium
    Embodied.medium
    Embodied.medium
    Embodied.low

immuneShiftedSameCore : AllostaticBodyState
immuneShiftedSameCore =
  allostaticBodyState
    Embodied.regulatedBody
    Embodied.medium
    Embodied.medium
    Embodied.medium
    Embodied.high

coreProjection : AllostaticBodyState → Embodied.BodyState
coreProjection = autonomicEndocrineCore

immuneProjection : AllostaticBodyState → Embodied.Activation
immuneProjection = immune

coreBodyDoesNotDetermineFullAllostaticState :
  NF.FactorsThrough coreProjection immuneProjection → ⊥
coreBodyDoesNotDetermineFullAllostaticState =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      regulatedExtended immuneShiftedSameCore refl (λ ()))

interoceptiveAfferenceOf : AllostaticBodyState → Embodied.InteroceptiveAfference
interoceptiveAfferenceOf state = Embodied.afference (autonomicEndocrineCore state)

sameCurrentAfferenceCanHideDifferentAllostaticCoordinates :
  interoceptiveAfferenceOf regulatedExtended
  ≡ interoceptiveAfferenceOf immuneShiftedSameCore
  × (regulatedExtended ≡ immuneShiftedSameCore → ⊥)
sameCurrentAfferenceCanHideDifferentAllostaticCoordinates = refl , (λ ())

record AllostaticBodyStateBoundary : Set where
  constructor allostaticBodyStateBoundary
  field
    cortisolIsCompleteBodyState : Bool
    autonomicCoreExhaustsAllostaticState : Bool
    currentAfferenceExhaustsAllostaticState : Bool
    multisystemVectorCarrierRetained : Bool

canonicalAllostaticBodyStateBoundary : AllostaticBodyStateBoundary
canonicalAllostaticBodyStateBoundary =
  allostaticBodyStateBoundary false false false true
