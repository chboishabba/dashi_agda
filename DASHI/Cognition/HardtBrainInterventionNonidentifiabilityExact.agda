module DASHI.Cognition.HardtBrainInterventionNonidentifiabilityExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineFabricCalculusExact as Fabric
import DASHI.Core.ContrastiveInterventionResponseExact as Intervention

------------------------------------------------------------------------
-- HARDT/BRAIN-IT/THALAMOCORTICAL CROSS-PR FINITE CAUSAL CUT
--
-- THIS IS A SOURCE-INDEPENDENT MATHEMATICAL COUNTEREXAMPLE, NOT A
-- HUMAN EEG, fMRI, MEG, DELTA TRAINING, MIND-READING OR PSI RESULT.
--
-- Original contributors retain their attribution: Core generic fabric
-- and contrastive intervention are existing DASHI owners; Brain-IT
-- Beliy et al. ICLR 2026 is an external fMRI reconstruction result.
-- dashiBRAIN PR #9 owns runnable finite consumer/commutation diagnostics.
--
-- Both microcausal worlds show the same passive input/output under
-- ordinary observation. Their outcomes differ under do(X:=true).
------------------------------------------------------------------------

data CausalModel : Set where
  directEffect : CausalModel
  sharedCauseOnly : CausalModel

record TrialWorld : Set where
  constructor world
  field
    sharedCue : Bool
    causalModel : CausalModel
open TrialWorld public

observedStimulus : TrialWorld → Bool
observedStimulus w = sharedCue w

observedOutcome : TrialWorld → Bool
observedOutcome w = sharedCue w

passiveObservation : TrialWorld → Bool × Bool
passiveObservation w = observedStimulus w , observedOutcome w

-- The contrast is do(X=0) versus do(X=1). For the witness U=0,\n-- the do(X=0) arm coincides with passive observation; this is NOT an\n-- assertion that forced-zero intervention is sham for every U.
-- In the direct model the receiving outcome follows a forced input.
-- In the shared-cause model it remains driven by its independent cue.
-- The toy is a finite structural causal model, not human neural physics.
interventionOutcome : Bool → TrialWorld → Bool
interventionOutcome imposed (world cue directEffect) = imposed
interventionOutcome imposed (world cue sharedCauseOnly) = cue

-- The generic ContrastiveInterventionResponse requires a true State
-- preserving transition, not a map directly from State to observed Bool.
-- Keep the original physical/causal world while recording the imposed X.
record InterventionState : Set where
  constructor intervention-state
  field
    currentInput : Bool
    originalWorld : TrialWorld
open InterventionState public

setInterventionInput : Bool → InterventionState → InterventionState
setInterventionInput b (intervention-state _ w) = intervention-state b w

readInterventionOutcome : InterventionState → Bool
readInterventionOutcome (intervention-state b w) =
  interventionOutcome b w

-- The inherited generic helper now receives its actual function types:
-- State=InterventionState; Intervention=Bool; Observation=Bool.
causalResponse : TrialWorld → Bool → Bool × Bool
causalResponse w action =
  Intervention.ContrastiveInterventionResponse
    readInterventionOutcome
    setInterventionInput
    false
    (λ control treated → control , treated)
    (intervention-state false w)
    action

sameCueDirect : TrialWorld
sameCueDirect = world false directEffect

sameCueConfounded : TrialWorld
sameCueConfounded = world false sharedCauseOnly

passivelyIndistinguishable :
  passiveObservation sameCueDirect ≡ passiveObservation sameCueConfounded
passivelyIndistinguishable = refl

differentCausalResponse :
  causalResponse sameCueDirect true ≡
  causalResponse sameCueConfounded true → ⊥
differentCausalResponse ()

-- The observation quotient is not a sufficient statistic for the
-- causal intervention consumer, even though its baseline fits perfectly.
counterexample : Fabric.ProjectionCollision
  passiveObservation (λ w → causalResponse w true)
counterexample = record
  { Fabric.ProjectionCollision.left = sameCueDirect
  ; Fabric.ProjectionCollision.right = sameCueConfounded
  ; Fabric.ProjectionCollision.sameProjection = refl
  ; Fabric.ProjectionCollision.consumerSeparates = differentCausalResponse
  }

noUniversalDoDecoder :
  (decoder : Bool × Bool → Bool × Bool) →
  ((w : TrialWorld) → causalResponse w true ≡
    decoder (passiveObservation w)) → ⊥
noUniversalDoDecoder =
  Fabric.consumerCannotFactorThroughProjection counterexample

-- ContrastiveInterventionResponseExact provides its more general descent
-- theorem. The same two worlds refute baseline-only intervention response.
noBaselineResponseDescent :
  Intervention.ResponseDescendsThroughBaseline
    readInterventionOutcome setInterventionInput false
    (λ control treated → control , treated) true → ⊥
noBaselineResponseDescent =
  Intervention.responseCollisionBlocksBaselineDescent
    {x = intervention-state false sameCueDirect}
    {y = intervention-state false sameCueConfounded}
    refl differentCausalResponse

------------------------------------------------------------------------
-- A causal distinction does not establish brain-source physical identity.
------------------------------------------------------------------------

data RealHumanDeltaAndFieldSourceReceipt : Set where
data BlindedInterventionObservationReceipt : Set where
data IndependentlyReplicatedReceiverEffect : Set where

record PhysicalPromotionReceipt : Set where
  field
    physiologicalSource : RealHumanDeltaAndFieldSourceReceipt
    interventionObservation : BlindedInterventionObservationReceipt
    replicatedCausality : IndependentlyReplicatedReceiverEffect
