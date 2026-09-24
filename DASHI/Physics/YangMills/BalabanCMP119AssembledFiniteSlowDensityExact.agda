module DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact where

------------------------------------------------------------------------
-- CMP119 ASSEMBLED DENSITY -> FINITE SLOW-FIELD RAW WEIGHTS
--
-- The generic CMP119FiniteSlowDensityRealization accepts a total
--
--   Density -> SlowField -> Q
--
-- interpreter.  That is stronger than the source consumer needs and permits a
-- representation to be chosen independently of the literal Section-2
-- construction.
--
-- Round219 already fixes, on the SAME beta-driven source family,
--
--   densityAt k
--     = assembleDensity (operationAt k) (effectiveActionAt k).
--
-- The preferred finite route therefore evaluates those exact assembled source
-- coordinates.  No arbitrary Density value is interpreted here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanFinitePositiveWeightNormalizationExact as Normalize
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact as Raw

record CMP119AssembledDensityFiniteEvaluator
    {trajectory split}
    {source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split}}
    (family : R219.BetaDrivenCMP119ResidualFamily source)
    (SlowField : Set) : Set₁ where
  field
    evaluateAssembledDensity :
      R219.Operation family →
      R219.Action family →
      SlowField → ℚ

open CMP119AssembledDensityFiniteEvaluator public

assembledSelectedWeight :
  ∀ {trajectory split source SlowField}
    {family : R219.BetaDrivenCMP119ResidualFamily
      {trajectory = trajectory} {split = split} source} →
  CMP119AssembledDensityFiniteEvaluator family SlowField →
  Nat → SlowField → ℚ
assembledSelectedWeight {family = family} evaluator cutoff =
  evaluateAssembledDensity evaluator
    (R219.operationAt family cutoff)
    (R219.effectiveActionAt family cutoff)

selectedSourceDensityIsAssembled :
  ∀ {trajectory split source}
    (family : R219.BetaDrivenCMP119ResidualFamily
      {trajectory = trajectory} {split = split} source)
    cutoff →
  Beta.densityAt source cutoff
  ≡ R219.assembleDensity family
      (R219.operationAt family cutoff)
      (R219.effectiveActionAt family cutoff)
selectedSourceDensityIsAssembled family cutoff =
  R219.densityEquation family cutoff

record CMP119AssembledFiniteSlowDensityRealization
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
      CMP119AssembledDensityFiniteEvaluator family SlowField) : Set₁ where
  field
    scaleAt : Nat → Scale
    componentAt : Nat → Component

    slowStatesAt : Nat → List SlowField

    selectedAssembledWeightNonnegative :
      ∀ cutoff slow →
      0ℚ ≤ assembledSelectedWeight evaluator cutoff slow

    positiveWitnessAt : Nat → SlowField

    positiveWitnessInStates : ∀ cutoff →
      PositiveMass._∈_
        (positiveWitnessAt cutoff)
        (slowStatesAt cutoff)

    positiveWitnessWeight : ∀ cutoff →
      Positive
        (assembledSelectedWeight evaluator cutoff
          (positiveWitnessAt cutoff))

open CMP119AssembledFiniteSlowDensityRealization public

assembledRawWeightFamily :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed evaluator} →
  CMP119AssembledFiniteSlowDensityRealization
    {trajectory = trajectory} {split = split}
    source family
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {construction = construction}
    referenceInputs typed evaluator →
  Nat → Normalize.FinitePositiveWeightFamily SlowField
assembledRawWeightFamily {evaluator = evaluator} realization cutoff = record
  { states = slowStatesAt realization cutoff
  ; rawWeight = assembledSelectedWeight evaluator cutoff
  ; rawWeightNonnegative =
      selectedAssembledWeightNonnegative realization cutoff
  ; positiveWitness = positiveWitnessAt realization cutoff
  ; positiveWitnessInStates =
      positiveWitnessInStates realization cutoff
  ; positiveWitnessWeight =
      positiveWitnessWeight realization cutoff
  }

compileAssembledSelectedDensityRawSlowLaw :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed evaluator}
    (realization :
      CMP119AssembledFiniteSlowDensityRealization
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed evaluator) →
  Nat → Raw.Gate4RawSlowFieldDensity referenceInputs typed
compileAssembledSelectedDensityRawSlowLaw
  {evaluator = evaluator} realization cutoff = record
  { scale = scaleAt realization cutoff
  ; component = componentAt realization cutoff
  ; rawSlowWeights =
      assembledRawWeightFamily realization cutoff
  }

cmp119AssembledDensitySameObjectCompilerLevel : ProofLevel
cmp119AssembledDensitySameObjectCompilerLevel = machineChecked

cmp119AssembledFiniteSlowDensityCompilerLevel : ProofLevel
cmp119AssembledFiniteSlowDensityCompilerLevel = machineChecked

-- Source-facing payments now have the correct granularity:
-- instantiate the finite evaluation of the literal assembled (T_k,A_k)
-- density, then prove positivity/support on that same finite slow-field family.
literalCMP119AssembledDensityEvaluatorLevel : ProofLevel
literalCMP119AssembledDensityEvaluatorLevel = conditional

literalCMP119AssembledWeightNonnegativeLevel : ProofLevel
literalCMP119AssembledWeightNonnegativeLevel = conditional

literalCMP119AssembledPositiveSupportLevel : ProofLevel
literalCMP119AssembledPositiveSupportLevel = conditional
