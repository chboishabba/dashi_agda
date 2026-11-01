module DASHI.Physics.YangMills.BalabanCMP119Round214BackedPhysicalEffectiveActionExact where

------------------------------------------------------------------------
-- ROUND214-BACKED SOURCE ACTION -> GENERATED PHYSICAL EFFECTIVE ACTION
--
-- Preferred B1 route:
--
--   Round219 Action
--      -> source-fixed Round214 real evaluation
--      -> selected CMP119 A_k(V)
--      -> generated physical effective action.
--
-- No independent Action -> SlowField -> EffectiveAction evaluator is accepted.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (Positive)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ActionEvaluationExact as R214Action
import DASHI.Physics.YangMills.BalabanCMP119PhysicalEffectiveActionRealizationExact as GeneratedRealization
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4ParameterizedEffectiveActionExact as Generated

record CMP119Round214BackedPhysicalEffectiveAction
    {trajectory split}
    (source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    (family : R219.BetaDrivenCMP119ResidualFamily source)
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs)
    (semantics :
      Assembly.CMP119FiniteDensityAssemblySemantics
        source family SlowField)
    (round214 :
      R214Action.BetaDrivenCMP119Round214ActionEvaluation
        source family) : Set₂ where
  field
    Traversal : Set

    scaleAt : Nat → Scale

    selectedAt : ∀ cutoff →
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        (scaleAt cutoff)

    comparisonAt : Nat →
      Relative.RelativeSixFactorComparison Scale Traversal

    physicalMeaningAt : ∀ cutoff →
      Relative.RelativeTPointwiseMeaning
        (PhysicalT.canonicalPhysicalTData construction)
        (comparisonAt cutoff)

    slowToBackground :
      SlowField → R214Action.Background round214

    actionBackend :
      Generated.ParameterizedPhysicalEffectiveAction
        {EffectiveAction = ℝ}
        construction

    round214SelectedActionIsGenerated :
      ∀ cutoff slow →
      R214Action.evaluateAction round214
        (R219.effectiveActionAt family cutoff)
        (slowToBackground slow)
      ≡
      Generated.generatedPhysicalEffectiveAction
        actionBackend
        (scaleAt cutoff)
        (selectedAt cutoff)
        slow

    operationActionUsesRound214Exponential :
      ∀ cutoff slow →
      Assembly.applyOperationAction semantics
        (R219.operationAt family cutoff)
        (R219.effectiveActionAt family cutoff)
        slow
      ≡
      Generated.exponentialOfNegativeAction actionBackend
        (R214Action.evaluateAction round214
          (R219.effectiveActionAt family cutoff)
          (slowToBackground slow))

    slowStatesAt : Nat → List SlowField

    positiveWitnessAt : Nat → SlowField

    positiveWitnessInStates : ∀ cutoff →
      PositiveMass._∈_
        (positiveWitnessAt cutoff)
        (slowStatesAt cutoff)

    positiveWitnessWeight : ∀ cutoff →
      Positive
        (Assembly.applyOperationAction semantics
          (R219.operationAt family cutoff)
          (R219.effectiveActionAt family cutoff)
          (positiveWitnessAt cutoff))

open CMP119Round214BackedPhysicalEffectiveAction public

compilePhysicalEffectiveActionRealization :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics round214} →
  (realization :
    CMP119Round214BackedPhysicalEffectiveAction
      {trajectory = trajectory} {split = split}
      source family
      {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
      {Component = Component} {Functional = Functional}
      {construction = construction}
      referenceInputs typed semantics round214) →
  GeneratedRealization.CMP119PhysicalEffectiveActionRealization
    source family referenceInputs typed semantics
compilePhysicalEffectiveActionRealization realization = record
  { GeneratedRealization.CMP119PhysicalEffectiveActionRealization.Traversal =
      Traversal realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.EffectiveAction =
      ℝ
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.scaleAt =
      scaleAt realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.selectedAt =
      selectedAt realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.comparisonAt =
      comparisonAt realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.physicalMeaningAt =
      physicalMeaningAt realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.actionBackend =
      actionBackend realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.evaluateSourceAction =
      λ action slow →
        R214Action.evaluateAction round214 action
          (slowToBackground realization slow)
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.selectedSourceActionIsGenerated =
      round214SelectedActionIsGenerated realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.operationActionUsesSourceExponential =
      operationActionUsesRound214Exponential realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.slowStatesAt =
      slowStatesAt realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.positiveWitnessAt =
      positiveWitnessAt realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.positiveWitnessInStates =
      positiveWitnessInStates realization
  ; GeneratedRealization.CMP119PhysicalEffectiveActionRealization.positiveWitnessWeight =
      positiveWitnessWeight realization
  }

round214BackedActionEvaluationCompilerLevel : ProofLevel
round214BackedActionEvaluationCompilerLevel = machineChecked

round214BackedPhysicalEffectiveActionCompilerLevel : ProofLevel
round214BackedPhysicalEffectiveActionCompilerLevel = machineChecked

-- B1a is compiler-owned once the source Round214 action evaluation and
-- SlowField->Background adapter are fixed.  The substantive B1b payment is now
-- the equality of that SAME source-authorized real action with the generated
-- physical action.
literalRound214SelectedActionIsGeneratedPhysicalActionLevel : ProofLevel
literalRound214SelectedActionIsGeneratedPhysicalActionLevel = conditional

literalOperationActionUsesRound214ExponentialLevel : ProofLevel
literalOperationActionUsesRound214ExponentialLevel = conditional

slowFieldToRound214BackgroundLevel : ProofLevel
slowFieldToRound214BackgroundLevel = conditional

physicalRealNegativeLogExponentialBackendLevel : ProofLevel
physicalRealNegativeLogExponentialBackendLevel = conditional

literalRound214BackedPositiveSupportLevel : ProofLevel
literalRound214BackedPositiveSupportLevel = conditional
