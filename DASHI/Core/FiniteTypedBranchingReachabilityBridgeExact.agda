module DASHI.Core.FiniteTypedBranchingReachabilityBridgeExact where

------------------------------------------------------------------------
-- FINITE TYPED BRANCHING -> ADMISSIBLE REACHABILITY BRIDGE
--
-- PRIMARY SOURCES / NEIGHBOURHOOD
--
-- Theodore E. Harris,
-- "The Theory of Branching Processes", Springer, 1963.
-- DOI: 10.1007/978-3-642-51866-9.
--
-- E. Seneta,
-- "Non-negative Matrices and Markov Chains", 2nd ed., Springer, 1981.
-- DOI: 10.1007/0-387-32792-4.
--
-- David Blackwell,
-- "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2) (1953), 265--272.
-- DOI: 10.1214/aoms/1177729032.
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977,
-- pp. 238--252. DOI: 10.1145/512950.512973.
--
-- SOURCE SCOPE
--
-- Harris/Seneta motivate finite typed branching and non-negative transition
-- structure. Blackwell calibrates consumer-relative sufficiency vocabulary.
-- Cousot--Cousot motivates keeping coarse abstraction separate from concrete
-- transition semantics. None is proof authority for the exact DASHI witness.
--
-- DASHI CONTRIBUTION
--
-- FiniteTypedBranchingKernelExact owns row masses/regimes. TypedDependencyCore
-- and AdmissibleReachability already own proof-bearing actions and finite
-- reachability. ConsumerDescentMinimalObserverExact and DynamicalQuotientSafety
-- already own static consumer sufficiency and same-trace dynamic safety.
--
-- This file composes those owners around one finite typed-branching witness.
-- The central exact result is:
--
--   equal row mass / equal local branching regime
--   != equal target reachability
--   != dynamic quotient safety.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FiniteTypedBranchingKernelExact as Kernel
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Core.StageTransitionBarrierExact as Barrier
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Core.DynamicalQuotientSafety as Dynamic

------------------------------------------------------------------------
-- Proof that a scaled offspring entry is actually available.
------------------------------------------------------------------------

data Positive : Nat → Set where
  positive : ∀ {n} → Positive (suc n)

record KernelSupportedVocabulary
    {Type Action : Set}
    (kernel : Kernel.FiniteTypedBranchingKernel Type) : Set₁ where
  constructor kernel-supported-vocabulary
  field
    actionSource : Action → Type
    actionTarget : Action → Type
    actionLabel : Action → String
    actionSupported :
      (action : Action) →
      Positive
        (Kernel.scaledOffspring kernel
          (actionSource action)
          (actionTarget action))

open KernelSupportedVocabulary public

kernelActionSystem :
  ∀ {Type Action : Set}
    {kernel : Kernel.FiniteTypedBranchingKernel Type} →
  KernelSupportedVocabulary {Type} {Action} kernel →
  Dependency.DependentActionSystem Type Action
kernelActionSystem vocabulary = record
  { Precondition = λ state action → state ≡ actionSource vocabulary action
  ; Postcondition = λ before action after → after ≡ actionTarget vocabulary action
  ; actionLabel = actionLabel vocabulary
  }

kernelActionAdmissible :
  ∀ {Type Action : Set}
    {kernel : Kernel.FiniteTypedBranchingKernel Type}
    (vocabulary : KernelSupportedVocabulary {Type} {Action} kernel)
    (action : Action) →
  Dependency.AdmissibleAction
    (kernelActionSystem vocabulary)
    (actionSource vocabulary action)
    action
kernelActionAdmissible vocabulary action = record
  { precondition = refl
  ; after = actionTarget vocabulary action
  ; postcondition = refl
  ; dependencyReceipt =
      "positive typed-kernel support admitted as one proof-bearing action"
  }

supportedActionGivesOneStepReachability :
  ∀ {Type Action : Set}
    {kernel : Kernel.FiniteTypedBranchingKernel Type}
    (vocabulary : KernelSupportedVocabulary {Type} {Action} kernel)
    (action : Action) →
  Reach.Reachable
    (kernelActionSystem vocabulary)
    (actionSource vocabulary action)
    (actionTarget vocabulary action)
supportedActionGivesOneStepReachability vocabulary action =
  Reach.reachableStep
    action
    (kernelActionAdmissible vocabulary action)
    Reach.reachableRefl

------------------------------------------------------------------------
-- Canonical equal-row-mass / different-reachability witness.
------------------------------------------------------------------------

data RouteType : Set where
  trapStart escapeStart trapped escapeGoal : RouteType

routeTypes : List RouteType
routeTypes = trapStart ∷ escapeStart ∷ trapped ∷ escapeGoal ∷ []

routeOffspring : RouteType → RouteType → Nat
routeOffspring trapStart trapped = 1
routeOffspring escapeStart escapeGoal = 1
routeOffspring trapped trapped = 1
routeOffspring _ _ = 0

routeKernel : Kernel.FiniteTypedBranchingKernel RouteType
routeKernel =
  Kernel.finite-typed-branching-kernel routeTypes routeOffspring 2

trapStartRowMassIsOne :
  Kernel.rowScaledMass routeKernel trapStart ≡ 1
trapStartRowMassIsOne = refl

escapeStartRowMassIsOne :
  Kernel.rowScaledMass routeKernel escapeStart ≡ 1
escapeStartRowMassIsOne = refl

sameStartRowMass :
  Kernel.rowScaledMass routeKernel trapStart
  ≡ Kernel.rowScaledMass routeKernel escapeStart
sameStartRowMass = refl

sameStartRowRegime :
  Kernel.rowRegime routeKernel trapStart
  ≡ Kernel.rowRegime routeKernel escapeStart
sameStartRowRegime = refl

data RouteAction : Set where
  enterTrap escapeDirectly stayTrapped : RouteAction

routeActionSource : RouteAction → RouteType
routeActionSource enterTrap = trapStart
routeActionSource escapeDirectly = escapeStart
routeActionSource stayTrapped = trapped

routeActionTarget : RouteAction → RouteType
routeActionTarget enterTrap = trapped
routeActionTarget escapeDirectly = escapeGoal
routeActionTarget stayTrapped = trapped

routeActionLabel : RouteAction → String
routeActionLabel enterTrap = "enter-trap"
routeActionLabel escapeDirectly = "escape-directly"
routeActionLabel stayTrapped = "stay-trapped"

routeActionSupported :
  (action : RouteAction) →
  Positive
    (Kernel.scaledOffspring routeKernel
      (routeActionSource action)
      (routeActionTarget action))
routeActionSupported enterTrap = positive
routeActionSupported escapeDirectly = positive
routeActionSupported stayTrapped = positive

routeVocabulary : KernelSupportedVocabulary {RouteType} {RouteAction} routeKernel
routeVocabulary =
  kernel-supported-vocabulary
    routeActionSource
    routeActionTarget
    routeActionLabel
    routeActionSupported

routeSystem : Dependency.DependentActionSystem RouteType RouteAction
routeSystem = kernelActionSystem routeVocabulary

escapeStartReachesGoal :
  Reach.Reachable routeSystem escapeStart escapeGoal
escapeStartReachesGoal =
  supportedActionGivesOneStepReachability routeVocabulary escapeDirectly

noTrappedToGoal :
  Reach.Reachable routeSystem trapped escapeGoal → ⊥
noTrappedToGoal
  (Reach.reachableStep enterTrap admissible rest)
  with Dependency.precondition admissible
... | ()
noTrappedToGoal
  (Reach.reachableStep escapeDirectly admissible rest)
  with Dependency.precondition admissible
... | ()
noTrappedToGoal
  (Reach.reachableStep stayTrapped admissible rest)
  with Dependency.postcondition admissible
... | refl = noTrappedToGoal rest

trapStartCannotReachGoal :
  Reach.Reachable routeSystem trapStart escapeGoal → ⊥
trapStartCannotReachGoal
  (Reach.reachableStep enterTrap admissible rest)
  with Dependency.postcondition admissible
... | refl = noTrappedToGoal rest
trapStartCannotReachGoal
  (Reach.reachableStep escapeDirectly admissible rest)
  with Dependency.precondition admissible
... | ()
trapStartCannotReachGoal
  (Reach.reachableStep stayTrapped admissible rest)
  with Dependency.precondition admissible
... | ()

------------------------------------------------------------------------
-- Cross-pollination into the existing barrier owner.
------------------------------------------------------------------------

canonicalTrapUnreachableUnderCurrentVocabulary :
  Barrier.UnreachableUnderCurrentVocabulary
    routeSystem trapStart escapeGoal
canonicalTrapUnreachableUnderCurrentVocabulary =
  Barrier.unreachable-under-current-vocabulary trapStartCannotReachGoal

canonicalTypedBranchTrapBarrier : Barrier.StageBarrierWitness
canonicalTypedBranchTrapBarrier =
  Barrier.stage-barrier-witness
    RouteType
    RouteAction
    routeSystem
    trapStart
    escapeGoal
    Barrier.trapBasinBarrier
    trapStartCannotReachGoal

------------------------------------------------------------------------
-- Static consumer non-descent: local row mass is too coarse for the declared
-- target-reachability consumer.
------------------------------------------------------------------------

data GoalReachabilityCode : Set where
  goalBlocked goalReachable : GoalReachabilityCode

goalReachabilityCode : RouteType → GoalReachabilityCode
goalReachabilityCode trapStart = goalBlocked
goalReachabilityCode escapeStart = goalReachable
goalReachabilityCode trapped = goalBlocked
goalReachabilityCode escapeGoal = goalReachable

rowMassCannotRecoverGoalReachabilityCode :
  Consumer.ConsumerNonDescentWitness
    (Kernel.rowScaledMass routeKernel)
    goalReachabilityCode
rowMassCannotRecoverGoalReachabilityCode =
  Consumer.consumerNonDescentWitness
    trapStart
    escapeStart
    sameStartRowMass
    (λ ())

rowMassIsNotConsumerSufficientForGoalReachability :
  Consumer.ConsumerSufficient
    (Kernel.rowScaledMass routeKernel)
    goalReachabilityCode →
  ⊥
rowMassIsNotConsumerSufficientForGoalReachability =
  Consumer.nonDescentWitnessBlocksSufficiency
    rowMassCannotRecoverGoalReachabilityCode

record GoalReachabilityCodeCalibration : Set where
  constructor goal-reachability-code-calibration
  field
    blockedCodeBackedByNoPath :
      Reach.Reachable routeSystem trapStart escapeGoal → ⊥
    reachableCodeBackedByPath :
      Reach.Reachable routeSystem escapeStart escapeGoal

canonicalGoalReachabilityCodeCalibration : GoalReachabilityCodeCalibration
canonicalGoalReachabilityCodeCalibration =
  goal-reachability-code-calibration
    trapStartCannotReachGoal
    escapeStartReachesGoal

------------------------------------------------------------------------
-- Dynamic quotient-safety witness, inspired by the existing parental-fear and
-- hidden-state future-defect lanes: the SAME consumer-visible action is applied
-- to two coarse-equal current states, but the future coarse observations differ.
--
-- The action system below is separately calibrated against the two positive
-- routeKernel entries. It is not a new branching kernel.
------------------------------------------------------------------------

data SharedAction : Set where
  advance : SharedAction

data AdvancePrecondition : RouteType → SharedAction → Set where
  advanceFromTrapStart : AdvancePrecondition trapStart advance
  advanceFromEscapeStart : AdvancePrecondition escapeStart advance

data AdvancePostcondition : RouteType → SharedAction → RouteType → Set where
  advanceIntoTrap : AdvancePostcondition trapStart advance trapped
  advanceIntoGoal : AdvancePostcondition escapeStart advance escapeGoal

sharedAdvanceSystem : Dependency.DependentActionSystem RouteType SharedAction
sharedAdvanceSystem = record
  { Precondition = AdvancePrecondition
  ; Postcondition = AdvancePostcondition
  ; actionLabel = λ advance → "advance"
  }

trapAdvanceAdmissible :
  Dependency.AdmissibleAction sharedAdvanceSystem trapStart advance
trapAdvanceAdmissible = record
  { precondition = advanceFromTrapStart
  ; after = trapped
  ; postcondition = advanceIntoTrap
  ; dependencyReceipt =
      "shared advance follows positive trapStart -> trapped kernel support"
  }

escapeAdvanceAdmissible :
  Dependency.AdmissibleAction sharedAdvanceSystem escapeStart advance
escapeAdvanceAdmissible = record
  { precondition = advanceFromEscapeStart
  ; after = escapeGoal
  ; postcondition = advanceIntoGoal
  ; dependencyReceipt =
      "shared advance follows positive escapeStart -> escapeGoal kernel support"
  }

trapAdvanceKernelSupported :
  Positive (Kernel.scaledOffspring routeKernel trapStart trapped)
trapAdvanceKernelSupported = positive

escapeAdvanceKernelSupported :
  Positive (Kernel.scaledOffspring routeKernel escapeStart escapeGoal)
escapeAdvanceKernelSupported = positive

data RouteObservation : Set where
  currentBand trapBand goalBand : RouteObservation

routeObservation : RouteType → RouteObservation
routeObservation trapStart = currentBand
routeObservation escapeStart = currentBand
routeObservation trapped = trapBand
routeObservation escapeGoal = goalBand

sameCurrentRouteObservation :
  routeObservation trapStart ≡ routeObservation escapeStart
sameCurrentRouteObservation = refl

trapAdvanceExecution :
  Reach.Executes sharedAdvanceSystem (advance ∷ []) trapStart trapped
trapAdvanceExecution =
  Reach.executesCons trapAdvanceAdmissible Reach.executesNil

escapeAdvanceExecution :
  Reach.Executes sharedAdvanceSystem (advance ∷ []) escapeStart escapeGoal
escapeAdvanceExecution =
  Reach.executesCons escapeAdvanceAdmissible Reach.executesNil

futureRouteObservationsDiffer :
  routeObservation trapped ≡ routeObservation escapeGoal → ⊥
futureRouteObservationsDiffer ()

routeObservationTerminalisationDefect :
  Dynamic.TerminalisationDefect sharedAdvanceSystem routeObservation
routeObservationTerminalisationDefect =
  Dynamic.terminalisationDefect
    (advance ∷ [])
    trapStart
    escapeStart
    trapped
    escapeGoal
    sameCurrentRouteObservation
    trapAdvanceExecution
    escapeAdvanceExecution
    futureRouteObservationsDiffer

routeObservationIsDynamicallyUnsafe :
  Dynamic.DynamicConsumerSafety sharedAdvanceSystem routeObservation → ⊥
routeObservationIsDynamicallyUnsafe safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    routeObservationTerminalisationDefect

------------------------------------------------------------------------
-- Exact semantic conclusion: local count/regime is not reachability geometry.
------------------------------------------------------------------------

record EqualLocalBranchingDifferentReachability : Set₁ where
  constructor equal-local-branching-different-reachability
  field
    equalScaledMass :
      Kernel.rowScaledMass routeKernel trapStart
      ≡ Kernel.rowScaledMass routeKernel escapeStart
    equalRegime :
      Kernel.rowRegime routeKernel trapStart
      ≡ Kernel.rowRegime routeKernel escapeStart
    leftCannotReachGoal :
      Reach.Reachable routeSystem trapStart escapeGoal → ⊥
    rightCanReachGoal :
      Reach.Reachable routeSystem escapeStart escapeGoal
    rowMassInsufficientForGoalConsumer :
      Consumer.ConsumerSufficient
        (Kernel.rowScaledMass routeKernel)
        goalReachabilityCode →
      ⊥

canonicalEqualLocalBranchingDifferentReachability :
  EqualLocalBranchingDifferentReachability
canonicalEqualLocalBranchingDifferentReachability =
  equal-local-branching-different-reachability
    sameStartRowMass
    sameStartRowRegime
    trapStartCannotReachGoal
    escapeStartReachesGoal
    rowMassIsNotConsumerSufficientForGoalReachability

record TypedBranchingReachabilityBoundary : Set where
  constructor typed-branching-reachability-boundary
  field
    rowMassDeterminesTargetReachability : Bool
    rowMassDeterminesTargetReachabilityIsFalse :
      rowMassDeterminesTargetReachability ≡ false
    rowRegimeDeterminesTargetReachability : Bool
    rowRegimeDeterminesTargetReachabilityIsFalse :
      rowRegimeDeterminesTargetReachability ≡ false
    positiveKernelEntryAloneProvesGlobalEscape : Bool
    positiveKernelEntryAloneProvesGlobalEscapeIsFalse :
      positiveKernelEntryAloneProvesGlobalEscape ≡ false
    sameCurrentObservationGuaranteesSameFutureObservation : Bool
    sameCurrentObservationGuaranteesSameFutureObservationIsFalse :
      sameCurrentObservationGuaranteesSameFutureObservation ≡ false
    reachabilityUsesExistingAdmissibleClosure : Bool
    reachabilityUsesExistingAdmissibleClosureIsTrue :
      reachabilityUsesExistingAdmissibleClosure ≡ true

canonicalTypedBranchingReachabilityBoundary :
  TypedBranchingReachabilityBoundary
canonicalTypedBranchingReachabilityBoundary =
  typed-branching-reachability-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
