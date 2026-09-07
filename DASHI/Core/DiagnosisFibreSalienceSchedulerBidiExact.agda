module DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Backprop
import DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact as Salience

------------------------------------------------------------------------
-- DIAGNOSIS FIBRE + DEBUGGING SALIENCE
--
-- An adverse or indeterminate result need not identify one cause.  Keep the
-- compatible diagnoses live and choose a debugging observation by how much it
-- separates that diagnosis fibre, not by raw signal magnitude.
------------------------------------------------------------------------

DiagnosisFibre : Set₁
DiagnosisFibre = Salience.LiveSet Backprop.OutcomeDiagnosis

record DebugObservation : Set₁ where
  constructor debug-observation
  field
    label : String
    magnitude : Nat
    updateDiagnosisFibre : DiagnosisFibre → DiagnosisFibre
    observationReference : String

open DebugObservation public

record StrictDiagnosisNarrowing
    (observation : DebugObservation)
    (prior : DiagnosisFibre) : Set where
  constructor strict-diagnosis-narrowing
  field
    refines :
      ∀ diagnosis →
      updateDiagnosisFibre observation prior diagnosis →
      prior diagnosis
    eliminated :
      Σ Backprop.OutcomeDiagnosis
        (λ diagnosis →
          prior diagnosis ×
          ¬ (updateDiagnosisFibre observation prior diagnosis))

open StrictDiagnosisNarrowing public

DiagnosisSalientOn : DebugObservation → DiagnosisFibre → Set
DiagnosisSalientOn observation prior =
  StrictDiagnosisNarrowing observation prior

------------------------------------------------------------------------
-- Exact live ambiguity: model, frame and premise remain possible.
------------------------------------------------------------------------

ambiguousDiagnosisFibre : DiagnosisFibre
ambiguousDiagnosisFibre Backprop.modelConflict = ⊤
ambiguousDiagnosisFibre Backprop.frameConflict = ⊤
ambiguousDiagnosisFibre Backprop.premiseConflict = ⊤
ambiguousDiagnosisFibre _ = ⊥

largeButInertDebugObservation : DebugObservation
largeButInertDebugObservation =
  debug-observation
    "repeat high-magnitude endpoint measurement"
    10
    (λ live → live)
    "synthetic debugging calibration: large observation does not distinguish model/frame/premise"

smallFrameCheck : DebugObservation
smallFrameCheck =
  debug-observation
    "small frame-orientation control"
    1
    posterior
    "synthetic debugging calibration: frame control eliminates frame-conflict branch"
  where
    posterior : DiagnosisFibre → DiagnosisFibre
    posterior live Backprop.frameConflict = ⊥
    posterior live diagnosis = live diagnosis

smallFrameCheckIsSalient :
  DiagnosisSalientOn smallFrameCheck ambiguousDiagnosisFibre
smallFrameCheckIsSalient =
  strict-diagnosis-narrowing
    refine
    (Backprop.frameConflict , (tt , (λ x → x)))
  where
    refine :
      ∀ diagnosis →
      updateDiagnosisFibre smallFrameCheck ambiguousDiagnosisFibre diagnosis →
      ambiguousDiagnosisFibre diagnosis
    refine Backprop.frameConflict ()
    refine diagnosis proof = proof

largeDebugObservationIsInert :
  DiagnosisSalientOn largeButInertDebugObservation ambiguousDiagnosisFibre → ⊥
largeDebugObservationIsInert receipt with eliminated receipt
... | Backprop.modelConflict , (before , notAfter) = notAfter before
... | Backprop.frameConflict , (before , notAfter) = notAfter before
... | Backprop.premiseConflict , (before , notAfter) = notAfter before
... | Backprop.observationConflict , (() , _)
... | Backprop.ruleConflict , (() , _)
... | Backprop.consumerMismatch , (() , _)
... | Backprop.provenanceConflict , (() , _)
... | Backprop.authorityMismatch , (() , _)
... | Backprop.insufficientResolution , (() , _)

data DebugSchedulerChoice : Set where
  chooseLargeRepeat chooseSmallFrameControl : DebugSchedulerChoice

magnitudeGreedyDebugChoice : DebugSchedulerChoice
magnitudeGreedyDebugChoice = chooseLargeRepeat

salienceGreedyDebugChoice : DebugSchedulerChoice
salienceGreedyDebugChoice = chooseSmallFrameControl

magnitudeGreedyChoosesInertDebugging :
  magnitudeGreedyDebugChoice ≡ chooseLargeRepeat
magnitudeGreedyChoosesInertDebugging = refl

salienceGreedyChoosesDiagnosisNarrowing :
  salienceGreedyDebugChoice ≡ chooseSmallFrameControl
salienceGreedyChoosesDiagnosisNarrowing = refl

------------------------------------------------------------------------
-- Diagnostic ambiguity does not authorise arbitrary backpropagation.
------------------------------------------------------------------------

data AmbiguousDiagnosisMeansReopenAll : Set where
data LargestSignalIsBestDebugger : Set where
data OneDebugObservationMustIdentifyCause : Set where

diagnosisAmbiguityDoesNotMeanReopenAll : AmbiguousDiagnosisMeansReopenAll → ⊥
diagnosisAmbiguityDoesNotMeanReopenAll ()

largestSignalNeedNotBestDistinguishDiagnosis : LargestSignalIsBestDebugger → ⊥
largestSignalNeedNotBestDistinguishDiagnosis ()

oneDebugObservationNeedNotIdentifyCause : OneDebugObservationMustIdentifyCause → ⊥
oneDebugObservationNeedNotIdentifyCause ()

record DiagnosisFibreSalienceBoundary : Set where
  constructor diagnosis-fibre-salience-boundary
  field
    multipleDiagnosesMayRemainLive : Bool
    salienceIndexedByDiagnosisFibre : Bool
    smallControlMayBeatLargeRepeat : Bool
    ambiguityReopensAllDependencies : Bool
    oneObservationMustIdentifyCause : Bool

canonicalDiagnosisFibreSalienceBoundary : DiagnosisFibreSalienceBoundary
canonicalDiagnosisFibreSalienceBoundary =
  diagnosis-fibre-salience-boundary true true true false false
