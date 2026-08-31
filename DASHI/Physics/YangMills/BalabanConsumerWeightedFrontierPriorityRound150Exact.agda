{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanConsumerWeightedFrontierPriorityRound150Exact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as R146
import DASHI.Physics.YangMills.BalabanFrontierExperimentDesignRound148Exact as R148

data FrontierConsumer : Set where
  densityActionConsumer
  a1PresentCutConsumer
  a2PresentCutConsumer
  bc1EffectiveActionConsumer
  bc2HeatDoobConsumer
  sectorStressConsumer
  qftgrStressConsumer
  : FrontierConsumer

leafConsumers : R146.BalabanFrontierLeaf → List FrontierConsumer
leafConsumers R146.densityActionRealization =
  bc1EffectiveActionConsumer ∷ bc2HeatDoobConsumer ∷
  sectorStressConsumer ∷ qftgrStressConsumer ∷ []
-- Direct/fallback prerequisites contribute to the action-realization state; no
-- one child inherits the whole route fanout before its siblings are closed.
leafConsumers R146.round108FixedDensitySemantics = densityActionConsumer ∷ []
leafConsumers R146.round108SelectedPotentialMatchesBC1 = densityActionConsumer ∷ []
leafConsumers R146.densityToCombinedRGState = densityActionConsumer ∷ []
leafConsumers R146.combinedRGStateToBC1Potential = densityActionConsumer ∷ []
leafConsumers R146.physicalCompositeD1ChainRule =
  bc1EffectiveActionConsumer ∷ sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.stressInsertionEqualsPhysicalD1Sum =
  sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.metricPerturbationAdmission =
  sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.a1CouplingToBetaHistory =
  a1PresentCutConsumer ∷ sectorStressConsumer ∷ []
leafConsumers R146.a2CouplingToBetaHistory =
  a2PresentCutConsumer ∷ sectorStressConsumer ∷ []
leafConsumers R146.cmp119FiniteMeasureSchwingerEndpoint =
  sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.unifiedSectorStressRecovery = qftgrStressConsumer ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

leafAlphaScore : R146.BalabanFrontierLeaf → Nat
leafAlphaScore leaf = listLength (leafConsumers leaf)

-- Route fanout belongs to the OR-state being solved, while route arity counts
-- declared AND prerequisites.  This keeps value and proof cost structurally
-- separate instead of crediting every child with its parent's fanout.
routeFanout : R146.BalabanFrontierRoute → Nat
routeFanout route = leafAlphaScore (R146.routeSource route)

routeArity : R146.BalabanFrontierRoute → Nat
routeArity route = listLength (R146.routeTargets route)

densityActionAlphaIsFour :
  leafAlphaScore R146.densityActionRealization ≡ suc (suc (suc (suc zero)))
densityActionAlphaIsFour = refl

round108SemanticsLeafAlphaIsOne :
  leafAlphaScore R146.round108FixedDensitySemantics ≡ suc zero
round108SemanticsLeafAlphaIsOne = refl

round108MatchLeafAlphaIsOne :
  leafAlphaScore R146.round108SelectedPotentialMatchesBC1 ≡ suc zero
round108MatchLeafAlphaIsOne = refl

physicalD1ChainRuleAlphaIsThree :
  leafAlphaScore R146.physicalCompositeD1ChainRule ≡ suc (suc (suc zero))
physicalD1ChainRuleAlphaIsThree = refl

directRound108RouteFanoutIsFour :
  routeFanout R146.directRound108ActionRoute ≡ suc (suc (suc (suc zero)))
directRound108RouteFanoutIsFour = refl

combinedRGRouteFanoutIsFour :
  routeFanout R146.viaCombinedRGActionRoute ≡ suc (suc (suc (suc zero)))
combinedRGRouteFanoutIsFour = refl

directRound108RouteArityIsTwo :
  routeArity R146.directRound108ActionRoute ≡ suc (suc zero)
directRound108RouteArityIsTwo = refl

combinedRGRouteArityIsTwo :
  routeArity R146.viaCombinedRGActionRoute ≡ suc (suc zero)
combinedRGRouteArityIsTwo = refl

record ConsumerWeightedPriority : Set₁ where
  field
    leaf : R146.BalabanFrontierLeaf
    route : R146.BalabanFrontierRoute
    routeTargetsLeaf : R146.routeSource route ≡ leaf
    admission : Least.RouteAdmission
    experimentCoordinate : R148.BalabanFrontierCoordinate
    experimentTargetsLeaf : R148.coordinateTargetsLeaf experimentCoordinate ≡ leaf

open ConsumerWeightedPriority public

priorityLiveSearch : ConsumerWeightedPriority → Least.LiveProofSearch
priorityLiveSearch receipt = Least.elaborateRoute (admission receipt)

record ConsumerWeightedPriorityBoundary : Set where
  constructor consumerWeightedPriorityBoundary
  field
    highestFanoutAutomaticallyProvesState : Bool
    highestFanoutAutomaticallyProvesStateIsFalse :
      highestFanoutAutomaticallyProvesState ≡ false
    onePrerequisiteMayClaimParentRouteFanout : Bool
    onePrerequisiteMayClaimParentRouteFanoutIsFalse :
      onePrerequisiteMayClaimParentRouteFanout ≡ false
    equalFanoutAndArityMakesRoutesScientificallyEquivalent : Bool
    equalFanoutAndArityMakesRoutesScientificallyEquivalentIsFalse :
      equalFanoutAndArityMakesRoutesScientificallyEquivalent ≡ false

canonicalConsumerWeightedPriorityBoundary : ConsumerWeightedPriorityBoundary
canonicalConsumerWeightedPriorityBoundary =
  consumerWeightedPriorityBoundary false refl false refl false refl

balabanConsumerWeightedFrontierPriorityLevel : ProofLevel
balabanConsumerWeightedFrontierPriorityLevel = machineChecked
