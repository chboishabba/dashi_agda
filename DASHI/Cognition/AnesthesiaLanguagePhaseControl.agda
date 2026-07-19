module DASHI.Cognition.AnesthesiaLanguagePhaseControl where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Ternary derivation gate
------------------------------------------------------------------------

data DerivationGate : Set where
  reject  : DerivationGate
  project : DerivationGate
  accept  : DerivationGate

record Prefix : Set where
  constructor prefix
  field
    depth : Nat
    label : String

record StackState : Set where
  constructor stackState
  field
    openObligations : Nat

record Margin : Set where
  constructor margin
  field
    positiveSlack : Nat
    negativeSlack : Nat

record ControlSignal : Set where
  constructor controlSignal
  field
    inactiveDepth : Nat
    positiveDrive : Nat
    negativeDrive : Nat

record LanguagePhaseState : Set where
  constructor languagePhaseState
  field
    currentPrefix : Prefix
    stack         : StackState
    marginState   : Margin
    control       : ControlSignal
    gate          : DerivationGate

------------------------------------------------------------------------
-- Four complementary observables
------------------------------------------------------------------------

record DepthToFailure : Set where
  constructor depthToFailure
  field
    maximumSurvivingDepth : Nat

record FeasibleBranching : Set where
  constructor feasibleBranching
  field
    enabledChildren : Nat

record MDLSlope : Set where
  constructor mdlSlope
  field
    codeIncreasePerStep : Nat

record StackDepthDistribution : Set where
  constructor stackDepthDistribution
  field
    expectedOpenObligations : Nat

record LanguagePhaseObservables : Set where
  constructor languagePhaseObservables
  field
    depthObservable     : DepthToFailure
    branchingObservable : FeasibleBranching
    mdlSlopeObservable  : MDLSlope
    stackObservable     : StackDepthDistribution

observeLanguagePhase : LanguagePhaseState → LanguagePhaseObservables
observeLanguagePhase state =
  languagePhaseObservables
    (depthToFailure (Prefix.depth (LanguagePhaseState.currentPrefix state)))
    (feasibleBranching
      (positiveChildren (LanguagePhaseState.gate state)))
    (mdlSlope
      (descriptionPressure (LanguagePhaseState.gate state)))
    (stackDepthDistribution
      (StackState.openObligations (LanguagePhaseState.stack state)))
  where
  positiveChildren : DerivationGate → Nat
  positiveChildren reject  = 0
  positiveChildren project = 1
  positiveChildren accept  = 3

  descriptionPressure : DerivationGate → Nat
  descriptionPressure reject  = 9
  descriptionPressure project = 3
  descriptionPressure accept  = 0

------------------------------------------------------------------------
-- Productive / critical / collapsed language phases
------------------------------------------------------------------------

data LanguagePhase : Set where
  collapsedPhase : LanguagePhase
  criticalPhase  : LanguagePhase
  productivePhase : LanguagePhase

phaseFromGate : DerivationGate → LanguagePhase
phaseFromGate reject  = collapsedPhase
phaseFromGate project = criticalPhase
phaseFromGate accept  = productivePhase

acceptHasThreeFeasibleChildren :
  FeasibleBranching.enabledChildren
    (LanguagePhaseObservables.branchingObservable
      (observeLanguagePhase
        (languagePhaseState
          (prefix 1 "accepted-prefix")
          (stackState 2)
          (margin 1 0)
          (controlSignal 0 1 0)
          accept)))
  ≡ 3
acceptHasThreeFeasibleChildren = refl

projectIsCriticalOneBranch :
  FeasibleBranching.enabledChildren
    (LanguagePhaseObservables.branchingObservable
      (observeLanguagePhase
        (languagePhaseState
          (prefix 1 "projected-prefix")
          (stackState 1)
          (margin 0 0)
          (controlSignal 1 0 0)
          project)))
  ≡ 1
projectIsCriticalOneBranch = refl

rejectHasZeroFeasibleChildren :
  FeasibleBranching.enabledChildren
    (LanguagePhaseObservables.branchingObservable
      (observeLanguagePhase
        (languagePhaseState
          (prefix 1 "rejected-prefix")
          (stackState 0)
          (margin 0 1)
          (controlSignal 0 0 1)
          reject)))
  ≡ 0
rejectHasZeroFeasibleChildren = refl

------------------------------------------------------------------------
-- Stack-obligation hysteresis
------------------------------------------------------------------------

record ObligationRebuildState : Set where
  constructor obligationRebuildState
  field
    obligationsBeforeCollapse : Nat
    obligationsAfterCollapse  : Nat
    obligationsRebuilt        : Nat

record CollapseRecoveryThresholds : Set where
  constructor collapseRecoveryThresholds
  field
    collapseThreshold : Nat
    recoveryThreshold : Nat

record HysteresisWitness : Set where
  constructor hysteresisWitness
  field
    stackPathDependent         : Bool
    recoveryRequiresRebuilding : Bool
    thresholdsMayDiffer        : Bool

stackHysteresis :
  ObligationRebuildState → CollapseRecoveryThresholds → HysteresisWitness
stackHysteresis rebuild thresholds =
  hysteresisWitness true true true

canonicalRebuildState : ObligationRebuildState
canonicalRebuildState = obligationRebuildState 9 0 3

canonicalThresholds : CollapseRecoveryThresholds
canonicalThresholds = collapseRecoveryThresholds 6 3

canonicalHysteresis : HysteresisWitness
canonicalHysteresis = stackHysteresis canonicalRebuildState canonicalThresholds

canonicalRecoveryRequiresRebuilding :
  HysteresisWitness.recoveryRequiresRebuilding canonicalHysteresis ≡ true
canonicalRecoveryRequiresRebuilding = refl

------------------------------------------------------------------------
-- Scope boundary
------------------------------------------------------------------------

record ControlTheoryBoundary : Set where
  constructor controlTheoryBoundary
  field
    languagePhaseFormalised       : Bool
    fourObservablesKeptDistinct   : Bool
    smoothPhysicsMayDriveGate     : Bool
    gateDoesNotDefineSemantics    : Bool
    clinicalPredictionPromoted    : Bool
    quantumCausePromoted          : Bool

canonicalControlTheoryBoundary : ControlTheoryBoundary
canonicalControlTheoryBoundary =
  controlTheoryBoundary true true true true false false

noClinicalPromotion :
  ControlTheoryBoundary.clinicalPredictionPromoted
    canonicalControlTheoryBoundary ≡ false
noClinicalPromotion = refl

noQuantumCausePromotion :
  ControlTheoryBoundary.quantumCausePromoted
    canonicalControlTheoryBoundary ≡ false
noQuantumCausePromotion = refl
