module DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationWeldExact where

------------------------------------------------------------------------
-- CMP119 ASSEMBLED DENSITY = PHYSICAL LOCALIZED T-OPERATION AT 1
--
-- This is the preferred source-faithful finite semantic weld.
--
-- It does NOT identify the physical density with the Gate4 reference majorant.
-- Instead it identifies the selected finite evaluation of the literal CMP119
-- assembled density with the physical T-operation itself.
--
-- Rational nonnegativity is then theorem-owned by the canonical physical
-- T-operation positivity result.  Strict positive support remains a separate
-- physical/support payment.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Assembled
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalPhysicalTOperationRationalNonnegativeExact as Nonnegative
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record CMP119PhysicalTOperationWeld
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
    (evaluator :
      Assembled.CMP119AssembledDensityFiniteEvaluator family SlowField) : Set₁ where
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

    slowStatesAt : Nat → List SlowField

    assembledDensityIsPhysicalTOperation : ∀ cutoff slow →
      Assembled.assembledSelectedWeight evaluator cutoff slow
      ≡
      T.localizedTOperation
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt cutoff)
        (selectedAt cutoff)
        slow
        (T.oneFunctional
          (PhysicalT.canonicalPhysicalTData construction))

    positiveWitnessAt : Nat → SlowField

    positiveWitnessInStates : ∀ cutoff →
      PositiveMass._∈_
        (positiveWitnessAt cutoff)
        (slowStatesAt cutoff)

    positiveWitnessWeight : ∀ cutoff →
      Positive
        (Assembled.assembledSelectedWeight evaluator cutoff
          (positiveWitnessAt cutoff))

open CMP119PhysicalTOperationWeld public

assembledPhysicalTOperationWeightNonnegative :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed evaluator}
    (weld :
      CMP119PhysicalTOperationWeld
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed evaluator)
    cutoff slow →
  Data.Rational.Base.0ℚ ≤
    Assembled.assembledSelectedWeight evaluator cutoff slow
assembledPhysicalTOperationWeightNonnegative
  {referenceInputs = referenceInputs}
  weld cutoff slow =
  Relation.Binary.PropositionalEquality.subst
    (λ value → Data.Rational.Base.0ℚ ≤ value)
    (Relation.Binary.PropositionalEquality.sym
      (assembledDensityIsPhysicalTOperation weld cutoff slow))
    (Nonnegative.canonicalPhysicalTOperationAtOneRationalNonnegative
      referenceInputs
      (physicalMeaningAt weld cutoff)
      (scaleAt weld cutoff)
      (selectedAt weld cutoff)
      slow)

compileCMP119PhysicalTOperationFiniteSlowDensityRealization :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed evaluator}
    (weld :
      CMP119PhysicalTOperationWeld
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed evaluator) →
  Assembled.CMP119AssembledFiniteSlowDensityRealization
    source family referenceInputs typed evaluator
compileCMP119PhysicalTOperationFiniteSlowDensityRealization weld = record
  { Assembled.CMP119AssembledFiniteSlowDensityRealization.scaleAt =
      scaleAt weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.componentAt =
      λ cutoff → T.component (selectedAt weld cutoff)
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.slowStatesAt =
      slowStatesAt weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.selectedAssembledWeightNonnegative =
      assembledPhysicalTOperationWeightNonnegative weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.positiveWitnessAt =
      positiveWitnessAt weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.positiveWitnessInStates =
      positiveWitnessInStates weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.positiveWitnessWeight =
      positiveWitnessWeight weld
  }

cmp119PhysicalTOperationWeightNonnegativeCompilerLevel : ProofLevel
cmp119PhysicalTOperationWeightNonnegativeCompilerLevel = machineChecked

cmp119PhysicalTOperationFiniteSlowDensityCompilerLevel : ProofLevel
cmp119PhysicalTOperationFiniteSlowDensityCompilerLevel = machineChecked

-- Genuine source same-object theorem.
literalCMP119AssembledDensityIsPhysicalTOperationLevel : ProofLevel
literalCMP119AssembledDensityIsPhysicalTOperationLevel = conditional

-- Strict support is not implied by mere nonnegativity of the physical density.
literalCMP119PhysicalTOperationPositiveSupportLevel : ProofLevel
literalCMP119PhysicalTOperationPositiveSupportLevel = conditional
