module DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementExact where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PhaseEnrichedTrit as Phase

------------------------------------------------------------------------
-- Structural continuous-oscillator refinement carrier.
--
-- Intended numerical realisation (not implemented or promoted here):
--
--   psi_i(t) = A_i exp(i(omega_i t + phi_i))
--   Psi(t)   = sum_i w_i psi_i(t)
--
-- The Agda carrier below deliberately records only the types and observation
-- boundaries required by such a producer.  In particular, ContinuousPhase is
-- not definitionally DASHI.Cognition.PhaseEnrichedTrit.Phase3, and HiddenField
-- is not claimed to be a Hilbert space or a complex vector space.
------------------------------------------------------------------------

record OscillatorSchema : Set₁ where
  field
    Mode : Set
    Amplitude : Set
    Frequency : Set
    ContinuousPhase : Set
    Coupling : Set
    HiddenField : Set

    assembleMode :
      Mode → Amplitude → Frequency → ContinuousPhase → Coupling → HiddenField

open OscillatorSchema public

record HiddenOscillatorState (O : OscillatorSchema) : Set where
  constructor hiddenOscillatorState
  field
    hiddenField : HiddenField O

open HiddenOscillatorState public

------------------------------------------------------------------------
-- Gauge / observational quotient seam.
--
-- A future numerical realisation may prove global-phase, time-origin, or
-- amplitude/weight rescaling symmetries.  This owner does not assume those
-- symmetries.  It only provides the relation and observer-soundness shape
-- needed once a concrete realisation supplies them.
------------------------------------------------------------------------

record HiddenObservationQuotient
  (Hidden Public : Set) : Set₁ where
  field
    EquivalentHiddenState : Hidden → Hidden → Set
    observe : Hidden → Public
    observerSound :
      ∀ x y → EquivalentHiddenState x y → observe x ≡ observe y

open HiddenObservationQuotient public

------------------------------------------------------------------------
-- Stable learned classes are deliberately broader than local minima.
------------------------------------------------------------------------

data StabilityRole : Set where
  localMinimum
  flatMinimum
  metastable
  phaseLocked
  limitCycleModGauge
  invariantLearnedClass : StabilityRole

record StableLearnedClass (Hidden : Set) : Set₁ where
  field
    LearnedClass : Set
    classify : Hidden → LearnedClass
    role : LearnedClass → StabilityRole

open StableLearnedClass public

------------------------------------------------------------------------
-- Objective, update and empirical/behavioural measurement remain distinct.
------------------------------------------------------------------------

record OscillatorObjectiveSurface (Hidden : Set) : Set₁ where
  field
    Objective : Set
    objective : Hidden → Objective

open OscillatorObjectiveSurface public

record LearningUpdateWitness (Hidden : Set) : Set₁ where
  field
    update : Hidden → Hidden

open LearningUpdateWitness public

record ObservedCognitiveMeasurement : Set₁ where
  field
    Measurement : Set

open ObservedCognitiveMeasurement public

------------------------------------------------------------------------
-- Refinement into the existing public memory and finite phase carriers.
--
-- The semantic identity preserved here is rememberedEvent.  Hidden oscillator
-- coordinates may therefore change while the public remembered event remains
-- the same.  A finite phase-bearing observation is supplied explicitly; no
-- identification between ContinuousPhase and Phase3 is made.
------------------------------------------------------------------------

record OscillatorMemoryRefinement (Hidden : Set) : Set₁ where
  field
    observeMemory : Hidden → Memory.MemoryFibre
    MemoryEquivalentHiddenState : Hidden → Hidden → Set
    preservedRememberedEvent :
      ∀ x y →
      MemoryEquivalentHiddenState x y →
      Memory.rememberedEvent (observeMemory x) ≡
      Memory.rememberedEvent (observeMemory y)

    observeFinitePhase : Hidden → Phase.PhaseEnrichedTrit

open OscillatorMemoryRefinement public

------------------------------------------------------------------------
-- WrongType / non-promotion boundary.
------------------------------------------------------------------------

record ContinuousOscillatorBoundary : Set₁ where
  field
    continuousPhaseIsNotPhase3ByDefinition : Set
    mismatchIsNotCognitiveDissonanceByDefinition : Set
    gradientDescentIsNotHebbianByDefinition : Set
    coherenceIsNotTruthByDefinition : Set
    stableClassIsNotMinimumByDefinition : Set
    targetStateIsNotBackwardsCausation : Set
    objectiveDoesNotMergeAllEnergyCarriers : Set

open ContinuousOscillatorBoundary public
