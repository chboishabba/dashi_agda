module DASHI.Physics.YangMills.BalabanCMP119Round214ExponentialPhysicalTBridgeExact where

------------------------------------------------------------------------
-- ROUND214 ACTION EXPONENTIAL = PHYSICAL GATE4 T-MASS
--
-- Preferred replacement for the generated -log action route.
--
-- Work in the real action semantics already authorized by Round214:
--
--   embed (applyOperationAction(T_k,A_k)(V))
--      = exp(- A_k^Round214(V))
--      = embed (T_phys(k,V) 1).
--
-- Injectivity of the selected rational->real embedding then recovers the
-- rational physical-T equality used by the finite normalization stack.
--
-- No logarithm is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ActionEvaluationExact as R214Action
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as PhysicalRealization
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record InjectiveRationalRealEmbedding : Set₁ where
  field
    embed : ℚ → ℝ
    injective : ∀ {left right} → embed left ≡ embed right → left ≡ right

open InjectiveRationalRealEmbedding public

record CMP119Round214ExponentialPhysicalTBridge
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

    rationalReal :
      InjectiveRationalRealEmbedding

    exponentialOfNegativeSourceAction :
      ℝ → ℝ

    -- B2, stated on the source-authorized Round214 action and only after
    -- embedding the finite rational density into the real action carrier.
    operationActionUsesRound214Exponential :
      ∀ cutoff slow →
      embed rationalReal
        (Assembly.applyOperationAction semantics
          (R219.operationAt family cutoff)
          (R219.effectiveActionAt family cutoff)
          slow)
      ≡
      exponentialOfNegativeSourceAction
        (R214Action.evaluateAction round214
          (R219.effectiveActionAt family cutoff)
          (slowToBackground slow))

    -- B1b': the SAME source action exponentiates to the SAME physical Gate4
    -- constrained T-mass at the unit functional.
    round214ExponentialIsPhysicalTOperation :
      ∀ cutoff slow →
      exponentialOfNegativeSourceAction
        (R214Action.evaluateAction round214
          (R219.effectiveActionAt family cutoff)
          (slowToBackground slow))
      ≡
      embed rationalReal
        (T.localizedTOperation
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt cutoff)
          (selectedAt cutoff)
          slow
          (T.oneFunctional
            (PhysicalT.canonicalPhysicalTData construction)))

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

open CMP119Round214ExponentialPhysicalTBridge public

operationActionIsPhysicalTOperation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics round214}
    (bridge :
      CMP119Round214ExponentialPhysicalTBridge
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed semantics round214)
    cutoff slow →
  Assembly.applyOperationAction semantics
    (R219.operationAt family cutoff)
    (R219.effectiveActionAt family cutoff)
    slow
  ≡
  T.localizedTOperation
    (PhysicalT.canonicalPhysicalTData construction)
    (scaleAt bridge cutoff)
    (selectedAt bridge cutoff)
    slow
    (T.oneFunctional
      (PhysicalT.canonicalPhysicalTData construction))
operationActionIsPhysicalTOperation bridge cutoff slow =
  injective (rationalReal bridge)
    (trans
      (operationActionUsesRound214Exponential bridge cutoff slow)
      (round214ExponentialIsPhysicalTOperation bridge cutoff slow))

compilePhysicalTOperationAssemblyRealization :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics round214} →
  (bridge :
    CMP119Round214ExponentialPhysicalTBridge
      {trajectory = trajectory} {split = split}
      source family
      {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
      {Component = Component} {Functional = Functional}
      {construction = construction}
      referenceInputs typed semantics round214) →
  PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization
    source family referenceInputs typed semantics
compilePhysicalTOperationAssemblyRealization bridge = record
  { PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.Traversal =
      Traversal bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.scaleAt =
      scaleAt bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.selectedAt =
      selectedAt bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.comparisonAt =
      comparisonAt bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.physicalMeaningAt =
      physicalMeaningAt bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.operationActionIsPhysicalTOperation =
      operationActionIsPhysicalTOperation bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.slowStatesAt =
      slowStatesAt bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessAt =
      positiveWitnessAt bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessInStates =
      positiveWitnessInStates bridge
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessWeight =
      positiveWitnessWeight bridge
  }

round214ExponentialPhysicalTCompilerLevel : ProofLevel
round214ExponentialPhysicalTCompilerLevel = machineChecked

round214ExponentialPhysicalTAssemblyCompilerLevel : ProofLevel
round214ExponentialPhysicalTAssemblyCompilerLevel = machineChecked

-- Preferred physical leaves.  No logarithm backend appears here.
literalOperationActionUsesRound214ExponentialLevel : ProofLevel
literalOperationActionUsesRound214ExponentialLevel = conditional

literalRound214ExponentialIsPhysicalTOperationLevel : ProofLevel
literalRound214ExponentialIsPhysicalTOperationLevel = conditional

slowFieldToRound214BackgroundLevel : ProofLevel
slowFieldToRound214BackgroundLevel = conditional

injectiveRationalRealEmbeddingLevel : ProofLevel
injectiveRationalRealEmbeddingLevel = conditional

literalRound214ExponentialPositiveSupportLevel : ProofLevel
literalRound214ExponentialPositiveSupportLevel = conditional
