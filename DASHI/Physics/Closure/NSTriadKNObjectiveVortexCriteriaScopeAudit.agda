module DASHI.Physics.Closure.NSTriadKNObjectiveVortexCriteriaScopeAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Tiemo Pedergnana; Florian Kogelbauer.
-- Title: "An Objective Q-Criterion".
-- Venue/year: arXiv preprint, 2025.
-- DOI: 10.48550/arXiv.2511.15777.
-- Uses: classification of objective Eulerian vortex-identification criteria.
-- Relationship: these criteria diagnose coherent vortex regions in a supplied
-- velocity field.  They do not by themselves provide a coercive Lyapunov
-- functional, a vortex-stretching depletion estimate, a commutator gain, or a
-- cutoff-uniform signed-class bound.  They are therefore retained as possible
-- diagnostics only and excluded from the active analytic closure path.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data VortexCriterionRole : Set where
  diagnostic analyticEstimate : VortexCriterionRole

objectiveQCriterionRole : VortexCriterionRole
objectiveQCriterionRole = diagnostic

objectiveQSuppliesCoerciveQuadraticForm : Bool
objectiveQSuppliesCoerciveQuadraticForm = false

objectiveQSuppliesCoerciveQuadraticFormIsFalse :
  objectiveQSuppliesCoerciveQuadraticForm ≡ false
objectiveQSuppliesCoerciveQuadraticFormIsFalse = refl

objectiveQSuppliesCommutatorGain : Bool
objectiveQSuppliesCommutatorGain = false

objectiveQSuppliesCommutatorGainIsFalse :
  objectiveQSuppliesCommutatorGain ≡ false
objectiveQSuppliesCommutatorGainIsFalse = refl

objectiveQSuppliesUniformQuarticDomination : Bool
objectiveQSuppliesUniformQuarticDomination = false

objectiveQSuppliesUniformQuarticDominationIsFalse :
  objectiveQSuppliesUniformQuarticDomination ≡ false
objectiveQSuppliesUniformQuarticDominationIsFalse = refl
