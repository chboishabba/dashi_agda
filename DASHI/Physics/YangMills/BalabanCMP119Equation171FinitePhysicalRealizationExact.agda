module DASHI.Physics.YangMills.BalabanCMP119Equation171FinitePhysicalRealizationExact where

------------------------------------------------------------------------
-- CMP119 SOURCE APPLICATION + STRUCTURED EQ.(1.71) FINITE REALIZATION
--   -> GATE4 PHYSICAL T-OPERATION
--
-- The former monolithic F1b-2 field is gone from this preferred API.
-- It is compiled from the Eq.(1.71) finite-realization ABI:
--
--   G1 fibre
--   G2 selector
--   G3 integrand/factors
--   G4 localized integral -> finite selected fold
--
-- plus the existing rational->real embedding and equality reflection.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119FiniteDensityAssemblySemanticsExact as Assembly
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171FiniteConstrainedRealizationExact as Finite
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanCMP119PhysicalTOperationAssemblyRealizationExact as PhysicalRealization
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record CMP119Equation171FinitePhysicalRealization
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
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding)
    (finite :
      Finite.CMP122Equation171FiniteConstrainedRealization
        construction sourceT embedding) : Set₂ where
  field
    Traversal : Set

    comparisonAt : Nat →
      Relative.RelativeSixFactorComparison Scale Traversal

    physicalMeaningAt : ∀ cutoff →
      Relative.RelativeTPointwiseMeaning
        (PhysicalT.canonicalPhysicalTData construction)
        (comparisonAt cutoff)

    -- F1b-1 only: meaning of the selected CMP119 source application.
    sourceApplicationIsEquation171Mass :
      ∀ cutoff slow →
      Finite.embedQ embedding
        (Assembly.applyOperationAction semantics
          (R219.operationAt family cutoff)
          (R219.effectiveActionAt family cutoff)
          slow)
      ≡
      Eq171.sourceTOperationMass sourceT cutoff slow

    -- Foundational equality reflection for this already-existing ring embedding.
    embeddingInjective :
      ∀ {left right : ℚ} →
      Finite.embedQ embedding left ≡ Finite.embedQ embedding right →
      left ≡ right

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

open CMP119Equation171FinitePhysicalRealization public

operationActionIsPhysicalTOperation :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics sourceT embedding finite}
    (realization :
      CMP119Equation171FinitePhysicalRealization
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed semantics sourceT embedding finite)
    cutoff slow →
  Assembly.applyOperationAction semantics
    (R219.operationAt family cutoff)
    (R219.effectiveActionAt family cutoff)
    slow
  ≡
  T.localizedTOperation
    (PhysicalT.canonicalPhysicalTData construction)
    (Finite.scaleAt finite cutoff)
    (Finite.selectedAt finite cutoff)
    slow
    (T.oneFunctional
      (PhysicalT.canonicalPhysicalTData construction))
operationActionIsPhysicalTOperation realization cutoff slow =
  embeddingInjective realization
    (trans
      (sourceApplicationIsEquation171Mass realization cutoff slow)
      (Finite.equation171SourceMassIsEmbeddedGate4TOperation
        _ cutoff slow))

compilePhysicalTOperationAssemblyRealization :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed semantics sourceT embedding finite} →
  (realization :
    CMP119Equation171FinitePhysicalRealization
      {trajectory = trajectory} {split = split}
      source family
      {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
      {Component = Component} {Functional = Functional}
      {construction = construction}
      referenceInputs typed semantics sourceT embedding finite) →
  PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization
    source family referenceInputs typed semantics
compilePhysicalTOperationAssemblyRealization
  {finite = finite} realization = record
  { PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.Traversal =
      Traversal realization
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.scaleAt =
      Finite.scaleAt finite
  ; PhysicalRealization.CMP119PhysicalTOperationAssemblyRealization.selectedAt =
      Finite.selectedAt finite
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

cmp119Equation171FinitePhysicalTOperationCompilerLevel : ProofLevel
cmp119Equation171FinitePhysicalTOperationCompilerLevel = machineChecked

cmp119Equation171FinitePhysicalAssemblyCompilerLevel : ProofLevel
cmp119Equation171FinitePhysicalAssemblyCompilerLevel = machineChecked

literalCMP119ApplicationIsEquation171MassLevel : ProofLevel
literalCMP119ApplicationIsEquation171MassLevel = conditional

rationalRealRingEmbeddingInjectivityLevel : ProofLevel
rationalRealRingEmbeddingInjectivityLevel = conditional

literalEquation171FinitePositiveSupportLevel : ProofLevel
literalEquation171FinitePositiveSupportLevel = conditional
