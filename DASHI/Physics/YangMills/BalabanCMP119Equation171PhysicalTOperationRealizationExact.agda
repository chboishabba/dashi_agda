module DASHI.Physics.YangMills.BalabanCMP119Equation171PhysicalTOperationRealizationExact where

------------------------------------------------------------------------
-- CMP119 SOURCE APPLICATION -> CMP122 EQ.(1.71) T-MASS -> GATE4 T-MASS
--
-- Canonical replacement for the over-compressed global exponential bridge.
--
-- Stage 1:
--   applying the selected CMP119 source operation/action pair means the same
--   source T-operation mass defined by CMP122 Eq. (1.71).
--
-- Stage 2:
--   that SAME Eq. (1.71) source T-mass is represented by the Gate4 finite
--   localized T-operation at the unit observable.
--
-- Rational->real injectivity recovers the exact rational equality consumed by
-- the finite probability stack.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (Positive)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP119Round214ExponentialPhysicalTBridgeExact as RealEmbed
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as PhysicalRealization
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record CMP119Equation171PhysicalTOperationRealization
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
    (sourceT :
      Eq171.CMP122Equation171TOperationSemantics
        Fine SlowField) : Set₂ where
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

    rationalReal :
      RealEmbed.InjectiveRationalRealEmbedding

    -- Meaning of the selected source T/A application:
    -- its finite scalar is the same source T-mass defined by Eq. (1.71).
    sourceApplicationIsEquation171Mass :
      ∀ cutoff slow →
      RealEmbed.embed rationalReal
        (Assembly.applyOperationAction semantics
          (R219.operationAt family cutoff)
          (R219.effectiveActionAt family cutoff)
          slow)
      ≡
      Eq171.sourceTOperationMass sourceT cutoff slow

    -- Concrete finite realization of the SAME source T-mass.
    equation171MassIsPhysicalTOperation :
      ∀ cutoff slow →
      Eq171.sourceTOperationMass sourceT cutoff slow
      ≡
      RealEmbed.embed rationalReal
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

open CMP119Equation171PhysicalTOperationRealization public

operationActionIsPhysicalTOperation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics sourceT}
    (realization :
      CMP119Equation171PhysicalTOperationRealization
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed semantics sourceT)
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
  RealEmbed.injective (rationalReal realization)
    (trans
      (sourceApplicationIsEquation171Mass realization cutoff slow)
      (equation171MassIsPhysicalTOperation realization cutoff slow))

compilePhysicalTOperationAssemblyRealization :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics sourceT} →
  (realization :
    CMP119Equation171PhysicalTOperationRealization
      {trajectory = trajectory} {split = split}
      source family
      {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
      {Component = Component} {Functional = Functional}
      {construction = construction}
      referenceInputs typed semantics sourceT) →
  PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization
    source family referenceInputs typed semantics
compilePhysicalTOperationAssemblyRealization realization = record
  { PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.Traversal =
      Traversal realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.scaleAt =
      scaleAt realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.selectedAt =
      selectedAt realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.comparisonAt =
      comparisonAt realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.physicalMeaningAt =
      physicalMeaningAt realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.operationActionIsPhysicalTOperation =
      operationActionIsPhysicalTOperation realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.slowStatesAt =
      slowStatesAt realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessAt =
      positiveWitnessAt realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessInStates =
      positiveWitnessInStates realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.positiveWitnessWeight =
      positiveWitnessWeight realization
  }

cmp119Equation171PhysicalTOperationCompilerLevel : ProofLevel
cmp119Equation171PhysicalTOperationCompilerLevel = machineChecked

cmp119Equation171PhysicalTOperationAssemblyCompilerLevel : ProofLevel
cmp119Equation171PhysicalTOperationAssemblyCompilerLevel = machineChecked

-- Remaining source/realization leaves on the canonical path.
literalCMP119ApplicationIsEquation171TOperationMassLevel : ProofLevel
literalCMP119ApplicationIsEquation171TOperationMassLevel = conditional

literalCMP122Equation171MassIsGate4PhysicalTOperationLevel : ProofLevel
literalCMP122Equation171MassIsGate4PhysicalTOperationLevel = conditional

injectiveRationalRealEmbeddingLevel : ProofLevel
injectiveRationalRealEmbeddingLevel = conditional

literalEquation171PhysicalTOperationPositiveSupportLevel : ProofLevel
literalEquation171PhysicalTOperationPositiveSupportLevel = conditional
