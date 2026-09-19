module DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact where

------------------------------------------------------------------------
-- CMP119 OPERATION/ACTION APPLICATION -> PHYSICAL T-OPERATION
--
-- This is the concrete second half of the finite source weld.
--
-- Combined with BalabanCMP119FiniteDensityAssemblySemanticsExact:
--
--   evaluate densityAt k
--     = applyOperationAction (operationAt k) (effectiveActionAt k)
--
-- and this module's physical realization:
--
--   applyOperationAction (operationAt k) (effectiveActionAt k)
--     = localizedTOperation physicalTData ... oneFunctional,
--
-- the older end-to-end CMP119PhysicalTOperationWeld is compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (Positive)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationWeldExact as Weld
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record CMP119PhysicalTOperationAssemblyRealization
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
        source family SlowField) : Set₁ where
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

    operationActionIsPhysicalTOperation :
      ∀ cutoff slow →
      Assembly.applyOperationAction semantics
        (R219.operationAt family cutoff)
        (R219.effectiveActionAt family cutoff)
        slow
      ≡
      T.localizedTOperation
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt cutoff)
        (selectedAt cutoff)
        slow
        (T.oneFunctional
          (PhysicalT.canonicalPhysicalTData construction))

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

open CMP119PhysicalTOperationAssemblyRealization public

compileEndToEndPhysicalTOperationWeld :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics} →
  (realization :
    CMP119PhysicalTOperationAssemblyRealization
      {trajectory = trajectory} {split = split}
      source family
      {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
      {Component = Component} {Functional = Functional}
      {construction = construction}
      referenceInputs typed semantics) →
  Weld.CMP119PhysicalTOperationWeld
    source family referenceInputs typed
    (Assembly.asAssembledDensityFiniteEvaluator semantics)
compileEndToEndPhysicalTOperationWeld realization = record
  { Weld.CMP119PhysicalTOperationWeld.Traversal =
      Traversal realization
  ; Weld.CMP119PhysicalTOperationWeld.scaleAt =
      scaleAt realization
  ; Weld.CMP119PhysicalTOperationWeld.selectedAt =
      selectedAt realization
  ; Weld.CMP119PhysicalTOperationWeld.comparisonAt =
      comparisonAt realization
  ; Weld.CMP119PhysicalTOperationWeld.physicalMeaningAt =
      physicalMeaningAt realization
  ; Weld.CMP119PhysicalTOperationWeld.slowStatesAt =
      slowStatesAt realization
  ; Weld.CMP119PhysicalTOperationWeld.assembledDensityIsPhysicalTOperation =
      operationActionIsPhysicalTOperation realization
  ; Weld.CMP119PhysicalTOperationWeld.positiveWitnessAt =
      positiveWitnessAt realization
  ; Weld.CMP119PhysicalTOperationWeld.positiveWitnessInStates =
      positiveWitnessInStates realization
  ; Weld.CMP119PhysicalTOperationWeld.positiveWitnessWeight =
      positiveWitnessWeight realization
  }

selectedSourceDensityEvaluationIsPhysicalTOperation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics}
    (realization :
      CMP119PhysicalTOperationAssemblyRealization
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed semantics)
    cutoff slow →
  Assembly.evaluateDensity semantics
    (Beta.densityAt source cutoff)
    slow
  ≡
  T.localizedTOperation
    (PhysicalT.canonicalPhysicalTData construction)
    (scaleAt realization cutoff)
    (selectedAt realization cutoff)
    slow
    (T.oneFunctional
      (PhysicalT.canonicalPhysicalTData construction))
selectedSourceDensityEvaluationIsPhysicalTOperation
  {semantics = semantics} realization cutoff slow =
  trans
    (Assembly.selectedDensityEvaluationIsAssembledWeight
      semantics cutoff slow)
    (operationActionIsPhysicalTOperation realization cutoff slow)

cmp119OperationActionPhysicalTOperationCompilerLevel : ProofLevel
cmp119OperationActionPhysicalTOperationCompilerLevel = machineChecked

cmp119EndToEndPhysicalTOperationWeldCompilerLevel : ProofLevel
cmp119EndToEndPhysicalTOperationWeldCompilerLevel = machineChecked

-- Concrete realization leaf: identify the selected source T_k/A_k application
-- with the physical Gate4 finite T-operation on the same cutoff carrier.
literalCMP119OperationActionIsPhysicalTOperationLevel : ProofLevel
literalCMP119OperationActionIsPhysicalTOperationLevel = conditional

-- Strict positive support remains independent of nonnegativity.
literalCMP119PhysicalTOperationPositiveSupportLevel : ProofLevel
literalCMP119PhysicalTOperationPositiveSupportLevel = conditional
