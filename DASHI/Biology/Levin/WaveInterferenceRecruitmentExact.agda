module DASHI.Biology.Levin.WaveInterferenceRecruitmentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_+_)
open import Data.Empty using (⊥)

import DASHI.Biology.Levin.NeuralWaveAnalogComputation as Analog

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- Earl K. Miller, Scott L. Brincat, Jefferson E. Roy,
-- "Analog Cognition and Consciousness" (2026), PsyArXiv preprint
-- DOI: 10.31234/osf.io/z48x7_v3.
--
-- The review proposes wave interference as an analog-computational substrate.
-- Direct signatures of that computation remain an empirical target.  This file
-- therefore proves only the exact algebra of a finite endpoint model: equal
-- in-phase amplitudes add; equal anti-phase amplitudes cancel; a nonzero
-- recruitment readout consequently changes.  It does not claim the cortex has
-- been proved to instantiate this finite model.
------------------------------------------------------------------------

data RelativePhase : Set where
  inPhase antiPhase : RelativePhase

combinedAmplitude : Nat → RelativePhase → Nat
combinedAmplitude amplitude inPhase = amplitude + amplitude
combinedAmplitude amplitude antiPhase = zero

constructiveInterferenceDoubles :
  (amplitude : Nat) →
  combinedAmplitude amplitude inPhase ≡ amplitude + amplitude
constructiveInterferenceDoubles amplitude = refl

destructiveInterferenceCancels :
  (amplitude : Nat) →
  combinedAmplitude amplitude antiPhase ≡ zero
destructiveInterferenceCancels amplitude = refl

nonzeroRecruit : Nat → Bool
nonzeroRecruit zero = false
nonzeroRecruit (suc _) = true

one : Nat
one = suc zero

two : Nat
two = suc one

unitInPhaseAmplitudeIsTwo :
  combinedAmplitude one inPhase ≡ two
unitInPhaseAmplitudeIsTwo = refl

unitAntiPhaseAmplitudeIsZero :
  combinedAmplitude one antiPhase ≡ zero
unitAntiPhaseAmplitudeIsZero = refl

inPhaseRecruits :
  nonzeroRecruit (combinedAmplitude one inPhase) ≡ true
inPhaseRecruits = refl

antiPhaseDoesNotRecruit :
  nonzeroRecruit (combinedAmplitude one antiPhase) ≡ false
antiPhaseDoesNotRecruit = refl

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

phaseDifferenceChangesRecruitment :
  nonzeroRecruit (combinedAmplitude one inPhase)
  ≡ nonzeroRecruit (combinedAmplitude one antiPhase) → ⊥
phaseDifferenceChangesRecruitment = trueNotFalse

------------------------------------------------------------------------
-- Adapter to the pre-existing analog-computation owner.  The computational
-- witness is stronger than a Boolean `analogComputation` label because the
-- input operation and output readout are explicit and the endpoint separation
-- above is theorem-bearing.
------------------------------------------------------------------------

amplitudeInteractionModel :
  Analog.WaveInteractionModel Nat Bool Bool
amplitudeInteractionModel = record
  { Analog.superpose = _+_
  ; Analog.readState = nonzeroRecruit
  ; Analog.interpretOutput = nonzeroRecruit
  ; Analog.parallelInteractionAvailable = true
  ; Analog.continuousAmplitudeAvailable = false
  ; Analog.interpretation =
      "finite endpoint realization of phase-sensitive superposition and recruitment"
  }

amplitudeComputationWitness :
  Analog.ComputationRealisationWitness amplitudeInteractionModel
amplitudeComputationWitness = record
  { Analog.inputEncodingSpecified = true
  ; Analog.operationSpecified = true
  ; Analog.outputDecodingSpecified = true
  ; Analog.commutingInterpretationDiagram = true
  ; Analog.perturbationPreservesPredictedRelation = true
  }

record WaveInterferenceBoundary : Set where
  constructor waveInterferenceBoundary
  field
    endpointAlgebraIsFullContinuousTrigTheory : Bool
    superpositionAloneProvesCorticalComputation : Bool
    computationImpliesPhenomenalConsciousness : Bool

canonicalWaveInterferenceBoundary : WaveInterferenceBoundary
canonicalWaveInterferenceBoundary =
  waveInterferenceBoundary false false false
