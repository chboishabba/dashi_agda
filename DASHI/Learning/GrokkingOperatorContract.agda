module DASHI.Learning.GrokkingOperatorContract where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_)
open import Ultrametric using (Ultrametric)
open import Contraction using (Contractive)
open import DASHI.Geometry.RGFlowContract using (RGFlowAxioms)

------------------------------------------------------------------------
-- DASHI learning contract
--
-- Learning is represented as an update operator together with an explicit
-- two-part description length.  The contract deliberately separates:
--
--   * data fit / residual code length;
--   * model / structure code length;
--   * the total MDL Lyapunov surface;
--   * contraction after entry into the rule basin.
--
-- This is the typed bridge from the existing RGFlowContract and COL surfaces
-- to machine-learning experiments.  It does not identify weight decay with
-- literal MDL; weight decay is an empirical proxy unless a separate coding
-- theorem is supplied.
------------------------------------------------------------------------

record LearningOperator (S : Set) : Set₁ where
  field
    step       : S → S
    dataCode   : S → Nat
    modelCode  : S → Nat
    totalMDL   : S → Nat

    totalMDL-def : ∀ s → totalMDL s ≡ dataCode s + modelCode s
    mdlMonotone : ∀ s → totalMDL (step s) ≤ totalMDL s

open LearningOperator public

------------------------------------------------------------------------
-- Metric closure: the same learner can be exposed through the existing
-- RG-flow contract once a metric and strict-contraction witness are supplied.
------------------------------------------------------------------------

record MetricLearningOperator (S : Set) : Set₁ where
  field
    learner : LearningOperator S
    metric  : Ultrametric S
    stepContractive : Contractive metric (LearningOperator.step learner)

open MetricLearningOperator public

asRGFlowAxioms : ∀ {S} → MetricLearningOperator S → RGFlowAxioms
asRGFlowAxioms {S} M = record
  { CouplingState = S
  ; U = metric M
  ; step = LearningOperator.step (learner M)
  ; mdl = LearningOperator.totalMDL (learner M)
  ; stepContractive = stepContractive M
  ; mdlMonotone = LearningOperator.mdlMonotone (learner M)
  }

------------------------------------------------------------------------
-- Grokking-time decomposition
--
-- The empirical transition is represented as a long crossing phase followed
-- by a shorter within-basin convergence phase.  This is the formal shape:
--
--   t-grok = t-cross + t-contract.
--
-- Quantitative bounds require concrete witnesses for both terms; the record
-- does not infer them from an accuracy plot.
------------------------------------------------------------------------

record GrokkingDecomposition : Set where
  field
    crossingEpoch    : Nat
    contractionEpoch : Nat
    grokEpoch        : Nat
    decomposition    : grokEpoch ≡ crossingEpoch + contractionEpoch

open GrokkingDecomposition public

------------------------------------------------------------------------
-- Horizon-aware observations
--
-- `rightCensored` means the threshold was not reached by the stated training
-- horizon.  `notRecorded` means the experiment output did not include that
-- statistic.  Neither constructor asserts impossibility.
------------------------------------------------------------------------

data FirstPassage : Set where
  notRecorded  : FirstPassage
  rightCensored : FirstPassage
  observedAt   : Nat → FirstPassage

record GrokkingObservation : Set where
  field
    horizon           : Nat
    fit99              : FirstPassage
    test95             : FirstPassage
    finalTrainPermille : Nat
    finalTestPermille  : Nat

open GrokkingObservation public
