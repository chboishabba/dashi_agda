module DASHI.Physics.YangMills.BalabanCMP119PhysicalEffectiveActionRealizationExact where

------------------------------------------------------------------------
-- SOURCE ACTION SEMANTICS -> PHYSICAL PARAMETERIZED EFFECTIVE ACTION
--
-- Factor the former joint F1b equality into:
--
--   B1. selected source A_k at slow
--         = generatedPhysicalEffectiveAction(k,slow)
--
--   B2. applyOperationAction(T_k,A_k) at slow
--         = exp(- selected source A_k at slow)
--
-- The generic exp(-log(.)) theorem then compiles
--
--   applyOperationAction(T_k,A_k)
--     = localized physical T-operation at one.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (Positive)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as PhysicalTRealization
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4ParameterizedEffectiveActionExact as Generated

record CMP119PhysicalEffectiveActionRealization
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
        source family SlowField) : Set₂ where
  field
    Traversal EffectiveAction : Set

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

    actionBackend :
      Generated.ParameterizedPhysicalEffectiveAction
        {EffectiveAction = EffectiveAction}
        construction

    evaluateSourceAction :
      R219.Action family → SlowField → EffectiveAction

    selectedSourceActionIsGenerated :
      ∀ cutoff slow →
      evaluateSourceAction
        (R219.effectiveActionAt family cutoff)
        slow
      ≡
      Generated.generatedPhysicalEffectiveAction
        actionBackend
        (scaleAt cutoff)
        (selectedAt cutoff)
        slow

    operationActionUsesSourceExponential :
      ∀ cutoff slow →
      Assembly.applyOperationAction semantics
        (R219.operationAt family cutoff)
        (R219.effectiveActionAt family cutoff)
        slow
      ≡
      Generated.exponentialOfNegativeAction actionBackend
        (evaluateSourceAction
          (R219.effectiveActionAt family cutoff)
          slow)

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

open CMP119PhysicalEffectiveActionRealization public

operationActionIsPhysicalTOperation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics}
    (realization :
      CMP119PhysicalEffectiveActionRealization
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed semantics)
    cutoff slow →
  Assembly.applyOperationAction semantics
    (R219.operationAt family cutoff)
    (R219.effectiveActionAt family cutoff)
    slow
  ≡
  T.localizedTOperation
    (PhysicalT.canonicalPhysicalTData construction)
    (scaleAt realization cutoff)
    (selectedAt realization cutoff)
    slow
    (T.oneFunctional
      (PhysicalT.canonicalPhysicalTData construction))
operationActionIsPhysicalTOperation realization cutoff slow =
  trans
    (operationActionUsesSourceExponential realization cutoff slow)
    (trans
      (cong
        (Generated.exponentialOfNegativeAction
          (actionBackend realization))
        (selectedSourceActionIsGenerated realization cutoff slow))
      (Generated.generatedPhysicalEffectiveActionDefinesTOperation
        (actionBackend realization)
        (scaleAt realization cutoff)
        (selectedAt realization cutoff)
        slow))

compilePhysicalTOperationAssemblyRealization :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics} →
  (realization :
    CMP119PhysicalEffectiveActionRealization
      {trajectory = trajectory} {split = split}
      source family
      {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
      {Component = Component} {Functional = Functional}
      {construction = construction}
      referenceInputs typed semantics) →
  PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization
    source family referenceInputs typed semantics
compilePhysicalTOperationAssemblyRealization realization = record
  { PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.Traversal =
      Traversal realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.scaleAt =
      scaleAt realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.selectedAt =
      selectedAt realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.comparisonAt =
      comparisonAt realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.physicalMeaningAt =
      physicalMeaningAt realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.operationActionIsPhysicalTOperation =
      operationActionIsPhysicalTOperation realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.slowStatesAt =
      slowStatesAt realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessAt =
      positiveWitnessAt realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessInStates =
      positiveWitnessInStates realization
  ; PhysicalTRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessWeight =
      positiveWitnessWeight realization
  }

cmp119PhysicalActionToTOperationCompilerLevel : ProofLevel
cmp119PhysicalActionToTOperationCompilerLevel = machineChecked

cmp119PhysicalTOperationAssemblyCompilerLevel : ProofLevel
cmp119PhysicalTOperationAssemblyCompilerLevel = machineChecked

-- F1b is now split into two source/realization payments.
literalCMP119SelectedActionIsGeneratedPhysicalActionLevel : ProofLevel
literalCMP119SelectedActionIsGeneratedPhysicalActionLevel = conditional

literalCMP119OperationActionUsesSourceExponentialLevel : ProofLevel
literalCMP119OperationActionUsesSourceExponentialLevel = conditional

-- The scalar negative-log / exp(-.) backend remains explicit.
physicalNegativeLogExponentialBackendLevel : ProofLevel
physicalNegativeLogExponentialBackendLevel = conditional

-- Strict positive support remains separate.
literalCMP119PhysicalTOperationPositiveSupportLevel : ProofLevel
literalCMP119PhysicalTOperationPositiveSupportLevel = conditional
