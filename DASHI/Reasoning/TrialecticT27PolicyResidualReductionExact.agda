module DASHI.Reasoning.TrialecticT27PolicyResidualReductionExact where

------------------------------------------------------------------------
-- HIDDEN T^27 POLICY AS AN EXACT CONSUMER-RELATIVE RESIDUAL
--
-- TrialecticT27PolicyHiddenNonDescentExact proves that forgetting the
-- completion policy collapses fine states which a third-face/policy consumer
-- can distinguish.  The repository-native ConsumerRelativeReduction kernel
-- lets us sharpen that statement constructively:
--
--   fine state = (hidden policy, free T^18)
--   reduced state = T^18
--   residual = hidden policy
--
-- and reduced state + residual reopen the fine state exactly.
--
-- For the declared T^18 observation, the reduction is future-safe under the
-- identity action.  The canonical collision is also an exact measurement
-- discriminator for the third T^9 face and a mechanistic-equifinality witness
-- for policy choice.  None of this turns policy labels into physical mechanism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27PolicyHiddenNonDescentExact as Hidden

------------------------------------------------------------------------
-- 1. Consumer-relative reduction: hide policy, retain exact T^18.
------------------------------------------------------------------------

identityFineStep : ⊤ → Hidden.PolicyTaggedT27 → Hidden.PolicyTaggedT27
identityFineStep tt state = state

identityReducedStep : ⊤ → Tower.T18Coordinates → Tower.T18Coordinates
identityReducedStep tt coordinates = coordinates

t18ConsumerReduction :
  Reduction.ConsumerRelativeReduction
    Hidden.PolicyTaggedT27
    ⊤
    Tower.T18Coordinates
t18ConsumerReduction =
  Reduction.consumerRelativeReduction
    Tower.T18Coordinates
    Hidden.observedT18
    identityFineStep
    identityReducedStep
    Hidden.observedT18
    (λ coordinates → coordinates)
    (λ action state → refl)
    (λ state → refl)

------------------------------------------------------------------------
-- 2. Exact residual reopening.  The information lost by the reduction is
--    precisely the policy choice for this tagged fine-state representation.
------------------------------------------------------------------------

reopenPolicy :
  Tower.T18Coordinates →
  Hidden.PolicyChoice →
  Hidden.PolicyTaggedT27
reopenPolicy coordinates policy =
  Hidden.policy-tagged-t27 policy coordinates

policyResidualReopening :
  Reduction.ExactResidualReopening t18ConsumerReduction
policyResidualReopening =
  Reduction.exactResidualReopening
    Hidden.PolicyChoice
    Hidden.hiddenPolicy
    reopenPolicy
    reopenExact
  where
  reopenExact :
    (state : Hidden.PolicyTaggedT27) →
    reopenPolicy
      (Reduction.encode t18ConsumerReduction state)
      (Hidden.hiddenPolicy state)
    ≡ state
  reopenExact (Hidden.policy-tagged-t27 policy coordinates) = refl

reopenPolicyExact :
  (state : Hidden.PolicyTaggedT27) →
  Reduction.reopen policyResidualReopening
    (Reduction.encode t18ConsumerReduction state)
    (Reduction.residual policyResidualReopening state)
  ≡ state
reopenPolicyExact = Reduction.reopenExact policyResidualReopening

------------------------------------------------------------------------
-- 3. The coarse code preserves its declared future consumer exactly.
------------------------------------------------------------------------

t18FuturePreserved :
  (actions : List ⊤) →
  (state : Hidden.PolicyTaggedT27) →
  Reduction.fineObserve t18ConsumerReduction
    (Reduction.run (Reduction.fineStep t18ConsumerReduction) actions state)
  ≡ Reduction.reducedObserve t18ConsumerReduction
      (Reduction.run (Reduction.reducedStep t18ConsumerReduction) actions
        (Reduction.encode t18ConsumerReduction state))
t18FuturePreserved = Reduction.consumerFuturePreserved t18ConsumerReduction

------------------------------------------------------------------------
-- 4. The canonical policy collision is separated by the third-face measure.
------------------------------------------------------------------------

thirdFaceDiscriminator :
  Reduction.MeasurementDiscriminator
    t18ConsumerReduction
    Hidden.firstPolicyState
    Hidden.secondPolicyState
thirdFaceDiscriminator =
  Reduction.measurementDiscriminator
    Tower.T9Coordinates
    Hidden.thirdFaceConsumer
    Hidden.sameObservedT18
    Hidden.differentThirdFace

policyMechanisticEquifinality :
  Reduction.MechanisticEquifinalityWitness t18ConsumerReduction
policyMechanisticEquifinality =
  Reduction.mechanisticEquifinalityWitness
    Hidden.PolicyChoice
    Hidden.policyConsumer
    Hidden.firstPolicyState
    Hidden.secondPolicyState
    Hidden.sameObservedT18
    Hidden.differentPolicyChoice

------------------------------------------------------------------------
-- 5. The third-face consumer does not descend through this reduction.  This
--    proof is stated directly on the reduction encoding, so no duplicate
--    factorisation record is introduced.
------------------------------------------------------------------------

thirdFaceDoesNotDescendThroughReduction :
  (realize : Tower.T18Coordinates → Tower.T9Coordinates) →
  ((state : Hidden.PolicyTaggedT27) →
    Hidden.thirdFaceConsumer state
    ≡ realize (Reduction.encode t18ConsumerReduction state)) →
  ⊥
thirdFaceDoesNotDescendThroughReduction realize commutes =
  Hidden.differentThirdFace
    (trans
      (commutes Hidden.firstPolicyState)
      (trans
        (cong realize Hidden.sameObservedT18)
        (sym (commutes Hidden.secondPolicyState))))

------------------------------------------------------------------------
-- 6. Promotion boundary.
------------------------------------------------------------------------

record TrialecticT27PolicyResidualReductionBoundary : Set where
  constructor trialectic-t27-policy-residual-reduction-boundary
  field
    t18ConsumerReductionConstructed : Bool
    hiddenPolicyExactResidualReopeningPaid : Bool
    thirdFaceMeasurementDiscriminatorPaid : Bool
    policyMechanisticEquifinalityPaid : Bool
    declaredT18FutureConsumerPreserved : Bool
    thirdFaceConsumerPreservedByT18Reduction : Bool
    residualIdentifiedAsPolicyChoice : Bool
    policyResidualPromotedToPhysicalMechanism : Bool

open TrialecticT27PolicyResidualReductionBoundary public

canonicalTrialecticT27PolicyResidualReductionBoundary :
  TrialecticT27PolicyResidualReductionBoundary
canonicalTrialecticT27PolicyResidualReductionBoundary =
  trialectic-t27-policy-residual-reduction-boundary
    true true true true true false true false

-- Re-export the canonical collision names for focused validation convenience.
firstPolicyState : Hidden.PolicyTaggedT27
firstPolicyState = Hidden.firstPolicyState
