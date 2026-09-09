module DASHI.Law.SensibLawWoogarooEPBCReformTransitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EPBC REFORM TRANSITION — EPBC 2019/8575
--
-- Source-bounded transition receipt for the 24 August 2026 commencement of
-- relevant Environment Protection Reform Act 2025 amendments.
-- This does not decide merits and does not substitute for counsel's
-- construction of the application/transitional provisions.
------------------------------------------------------------------------

record TransitionReceipt : Set where
  constructor transition-receipt
  field
    project : String
    referralPredatesCommencement : Bool
    assessmentApproachPredatesCommencement : Bool
    reformCommencement : String
    item683Relevant : Bool
    item690Relevant : Bool
    oldAssessmentFrameworkPotentiallyPreserved : Bool
    newPart9ThreatenedSpeciesRulesAutomaticallyApply : Bool
    counselConstructionStillRequired : Bool

open TransitionReceipt public

epbc8575Transition : TransitionReceipt
epbc8575Transition = transition-receipt
  "Springfield Residential Development — EPBC 2019/8575"
  true
  true
  "24 August 2026"
  true
  true
  true
  false
  true

------------------------------------------------------------------------
-- Typed boundaries.
------------------------------------------------------------------------

record TransitionBoundary : Set where
  constructor transition-boundary
  field
    currentActTextAloneDoesNotDetermineHistoricReferralRule : Bool
    reformCommencementDoesNotRestartReferral : Bool
    preCommencementReferralDoesNotMeanAllOldLawAutomaticallyApplies : Bool
    preCommencementAssessmentDoesNotMeanAllNewLawAutomaticallyApplies : Bool
    transitionalItemMustBeMatchedToExactProvision : Bool

transitionBoundary : TransitionBoundary
transitionBoundary = transition-boundary true true true true true

------------------------------------------------------------------------
-- Counsel residual.
------------------------------------------------------------------------

record TransitionResidual : Set where
  constructor transition-residual
  field
    question : String
    sourceState : String
    outcomeAlreadyProved : Bool

transitionResidual : TransitionResidual
transitionResidual = transition-residual
  "For EPBC 2019/8575, identify provision-by-provision which pre-24-August-2026 and post-24-August-2026 rules govern the pending Part 9 decision, including ss 134, 136, 138/139, recommendation-report/publication rules, and any applicable new powers or procedural duties."
  "Environment Protection Reform Act 2025 Schedule 1 Part 3 items 683 and 690 are directly relevant; August Commencements Transitional Rules 2026 must also be checked for any modifying rule."
  false
