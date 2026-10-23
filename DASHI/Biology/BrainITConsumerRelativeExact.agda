module DASHI.Biology.BrainITConsumerRelativeExact where

open import DASHI.Core.Prelude

import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Core.CoarseFineFabricCalculusExact as Fabric
import DASHI.Physics.Foundations.CoarseObservableFactorisationBidiExact as Coarse

------------------------------------------------------------------------
-- Reuse the CMS-facing generic consumer-relative factorisation calculus.
-- This finite neural witness is NOT a measurement of the actual Brain-IT
-- learned V2C map. It refutes an *universal* coarse decoder claim for the
-- already defined repo toy neural observation.
------------------------------------------------------------------------

-- A decoder's exact factorisation makes its consumer constant on every
-- fibre of the chosen measurement. No unprovided section is assumed.
factorisationRequiresFibreAgreement :
  {Output : Set}
  (consumer : Neural.PopulationActivation → Output) →
  (decoder : Neural.CoarseRegionalObservation → Output) →
  ((state : Neural.PopulationActivation) →
    consumer state ≡ decoder (Neural.fmriLikeObservation state)) →
  (left right : Neural.PopulationActivation) →
  Neural.fmriLikeObservation left ≡ Neural.fmriLikeObservation right →
  consumer left ≡ consumer right
factorisationRequiresFibreAgreement consumer decoder factors left right same =
  trans (factors left)
    (trans (cong decoder same) (sym (factors right)))

-- This consumer survives the projection, simply by definition.
coarseObservationConsumerRetained :
  (state : Neural.PopulationActivation) →
  Neural.fmriLikeObservation state ≡
    (λ measured → measured) (Neural.fmriLikeObservation state)
coarseObservationConsumerRetained state = refl

-- But the displayed fine-scale Laplacian observable does not.
-- The relevant counterexample is sourced in NeuralRepresentationLaplacianExact.
variationCollision :
  Fabric.ProjectionCollision
    Neural.fmriLikeObservation Neural.laplacianVariation
variationCollision = record
  { Fabric.ProjectionCollision.left = Neural.microActivationA
  ; Fabric.ProjectionCollision.right = Neural.microActivationB
  ; Fabric.ProjectionCollision.sameProjection =
      Neural.fmriProjectionCollision
  ; Fabric.ProjectionCollision.consumerSeparates = λ ()
  }

noUniversalLaplacianDecoder :
  (decoder : Neural.CoarseRegionalObservation → Nat) →
  ((state : Neural.PopulationActivation) →
    Neural.laplacianVariation state ≡
      decoder (Neural.fmriLikeObservation state)) →
  ⊥
noUniversalLaplacianDecoder =
  Coarse.collisionRefutesEveryCoarsePrediction
    Neural.fmriLikeObservation Neural.laplacianVariation
    variationCollision

-- Existing CMS-style no-promotion rule: a toy static collision is not
-- an empirical statement about performance on NSD, brain structure,
-- or a proof about physical neural mechanisms.
toyCollisionIsAnNSDBenchmark : Bool
toyCollisionIsAnNSDBenchmark = false

frozenPublishedMetricIsAnInKernelRecomputation : Bool
frozenPublishedMetricIsAnInKernelRecomputation = false

brainITConsumerRelativeTheoryValidation :
  toyCollisionIsAnNSDBenchmark ≡ false
  × frozenPublishedMetricIsAnInKernelRecomputation ≡ false
brainITConsumerRelativeTheoryValidation = refl , refl
