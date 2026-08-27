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
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977,
-- pp. 238--252. DOI: 10.1145/512950.512973.
--
-- SOURCE SCOPE
--
-- Harris/Seneta motivate finite typed branching and non-negative transition
-- structure. Cousot--Cousot motivates keeping a coarse abstraction separate
-- from concrete transition semantics. None of these sources is proof authority
-- for the exact DASHI bridge below.
--
-- DASHI CONTRIBUTION
--
-- FiniteTypedBranchingKernelExact owns row masses/regimes. TypedDependencyCore
-- and AdmissibleReachability already own proof-bearing actions and finite
-- reachability. This file connects them without defining a second graph or
-- reachability calculus.
--
-- The key theorem shape is deliberately stronger than branch counting:
--
--   equal row mass / equal local branching regime
--   != equal target reachability.
--
-- The concrete witness has two start states with the same scaled row mass and
-- same subcritical row regime. One reaches the declared goal in one admissible
-- step; the other enters a closed trap and cannot reach the goal at all.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FiniteTypedBranchingKernelExact as Kernel
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Core.StageTransitionBarrierExact as Barrier

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
-- Exact semantic conclusion: local row count/regime is not target reachability.
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

canonicalEqualLocalBranchingDifferentReachability :
  EqualLocalBranchingDifferentReachability
canonicalEqualLocalBranchingDifferentReachability =
  equal-local-branching-different-reachability
    sameStartRowMass
    sameStartRowRegime
    trapStartCannotReachGoal
    escapeStartReachesGoal

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
    true refl
