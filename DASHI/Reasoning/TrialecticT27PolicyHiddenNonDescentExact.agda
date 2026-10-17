module DASHI.Reasoning.TrialecticT27PolicyHiddenNonDescentExact where

------------------------------------------------------------------------
-- HIDDEN COMPLETION POLICY AS A CONSUMER-RELATIVE T^27 RESIDUAL
--
-- A fixed completion policy P : T^18 -> T^9 makes the completed graph exactly
-- recoverable from T^18.  If the policy itself is hidden, however, the same
-- observed T^18 state may extend to different third T^9 faces.  This is the
-- exact Nongin/consumer-descent pattern at the new T^27 carrier level.
--
-- Recent Goldbach/FRACTRAN sibling work independently uses the analogous rule
-- that fine machines may differ while a declared checkpoint consumer agrees.
-- That sibling is inspiration/provenance only here: the theorem below is proved
-- directly from the local T^18/T^27 graph carrier and existing consumer-descent
-- owner, with no imported theorem authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Reasoning.TrialecticC3GlobalNaturalityNoGoExact as C3NoGo
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower

------------------------------------------------------------------------
-- 1. Two explicit completion policies and one shared T^18 fixture.
------------------------------------------------------------------------

data PolicyChoice : Set where
  chooseFirstNine : PolicyChoice
  chooseSecondNine : PolicyChoice

choicePolicy : PolicyChoice → Tower.T27CompletionPolicy
choicePolicy chooseFirstNine = Tower.firstNine
choicePolicy chooseSecondNine = Tower.secondNine

originNine : Tower.T9Coordinates
originNine = Tower.t9-coordinates Fabric.origin Fabric.origin Fabric.origin

positiveNine : Tower.T9Coordinates
positiveNine =
  Tower.t9-coordinates Fabric.positiveCorner Fabric.origin Fabric.origin

selectedT18 : Tower.T18Coordinates
selectedT18 = Tower.t18-coordinates originNine positiveNine

originNineNotPositiveNine : originNine ≡ positiveNine → ⊥
originNineNotPositiveNine equality =
  C3NoGo.originNotPositiveCorner (cong Tower.coordinate0 equality)

------------------------------------------------------------------------
-- 2. Policy-tagged completed state.  The coarse observer deliberately forgets
--    the policy; the consumer asks for the third T^9 face.
------------------------------------------------------------------------

record PolicyTaggedT27 : Set where
  constructor policy-tagged-t27
  field
    hiddenPolicy : PolicyChoice
    freeCoordinates : Tower.T18Coordinates

open PolicyTaggedT27 public

ambientCube : PolicyTaggedT27 → Tower.T27Coordinates
ambientCube state =
  Tower.completeT27
    (choicePolicy (hiddenPolicy state))
    (freeCoordinates state)

observedT18 : PolicyTaggedT27 → Tower.T18Coordinates
observedT18 = freeCoordinates

thirdFaceConsumer : PolicyTaggedT27 → Tower.T9Coordinates
thirdFaceConsumer state = Tower.face2 (ambientCube state)

policyConsumer : PolicyTaggedT27 → PolicyChoice
policyConsumer = hiddenPolicy

firstPolicyState : PolicyTaggedT27
firstPolicyState = policy-tagged-t27 chooseFirstNine selectedT18

secondPolicyState : PolicyTaggedT27
secondPolicyState = policy-tagged-t27 chooseSecondNine selectedT18

sameObservedT18 :
  observedT18 firstPolicyState ≡ observedT18 secondPolicyState
sameObservedT18 = refl

differentThirdFace :
  thirdFaceConsumer firstPolicyState
  ≡ thirdFaceConsumer secondPolicyState
  →
  ⊥
differentThirdFace = originNineNotPositiveNine

differentPolicyChoice :
  policyConsumer firstPolicyState
  ≡ policyConsumer secondPolicyState
  →
  ⊥
differentPolicyChoice ()

------------------------------------------------------------------------
-- 3. Existing consumer-descent machinery turns the collision into exact
--    factorisation no-go theorems.
------------------------------------------------------------------------

thirdFaceNonDescentWitness :
  Descent.ConsumerNonDescentWitness observedT18 thirdFaceConsumer
thirdFaceNonDescentWitness =
  Descent.consumerNonDescentWitness
    firstPolicyState
    secondPolicyState
    sameObservedT18
    differentThirdFace

policyNonDescentWitness :
  Descent.ConsumerNonDescentWitness observedT18 policyConsumer
policyNonDescentWitness =
  Descent.consumerNonDescentWitness
    firstPolicyState
    secondPolicyState
    sameObservedT18
    differentPolicyChoice

policyHiddenThirdFaceDoesNotFactorThroughT18 :
  Descent.FactorsThrough observedT18 thirdFaceConsumer → ⊥
policyHiddenThirdFaceDoesNotFactorThroughT18 =
  Descent.nonDescentWitnessBlocksFactorization thirdFaceNonDescentWitness

hiddenPolicyDoesNotFactorThroughT18 :
  Descent.FactorsThrough observedT18 policyConsumer → ⊥
hiddenPolicyDoesNotFactorThroughT18 =
  Descent.nonDescentWitnessBlocksFactorization policyNonDescentWitness

------------------------------------------------------------------------
-- 4. Fixed-policy contrast: once P is declared, T^18 recovers the third face
--    definitionally.  The failure above is therefore policy-hidden residual
--    information, not a defect of the graph construction.
------------------------------------------------------------------------

recoverThirdFaceWithDeclaredPolicy :
  (policy : Tower.T27CompletionPolicy) →
  (coordinates : Tower.T18Coordinates) →
  Tower.face2 (Tower.completeT27 policy coordinates) ≡ policy coordinates
recoverThirdFaceWithDeclaredPolicy policy coordinates = refl

projectDeclaredCompletion :
  (policy : Tower.T27CompletionPolicy) →
  (coordinates : Tower.T18Coordinates) →
  Tower.projectT18 (Tower.completeT27 policy coordinates) ≡ coordinates
projectDeclaredCompletion = Tower.projectCompleteT27

------------------------------------------------------------------------
-- 5. Promotion boundary.
------------------------------------------------------------------------

record TrialecticT27PolicyHiddenNonDescentBoundary : Set where
  constructor trialectic-t27-policy-hidden-non-descent-boundary
  field
    sameT18DifferentThirdFaceWitnessPaid : Bool
    thirdFaceDoesNotFactorThroughT18 : Bool
    policyChoiceDoesNotFactorThroughT18 : Bool
    fixedPolicyThirdFaceRecoveredFromT18 : Bool
    fixedPolicyT18ProjectionRoundTrips : Bool
    policyHiddenResidualIsConsumerRelative : Bool
    hiddenPolicyChoicePromotedToPhysicalDynamics : Bool
    siblingCheckpointTheoremImportedAsLocalAuthority : Bool

open TrialecticT27PolicyHiddenNonDescentBoundary public

canonicalTrialecticT27PolicyHiddenNonDescentBoundary :
  TrialecticT27PolicyHiddenNonDescentBoundary
canonicalTrialecticT27PolicyHiddenNonDescentBoundary =
  trialectic-t27-policy-hidden-non-descent-boundary
    true true true true true true false false
