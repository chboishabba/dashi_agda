module DASHI.Physics.YangMills.BalabanCMP119FiniteSlowDensityRealizationExact where

------------------------------------------------------------------------
-- LITERAL CMP119 DENSITY -> FINITE SLOW-FIELD WEIGHTS
--
-- CMP119/CMP122 currently carries Density abstractly.  The finite probability
-- lane needs an actual evaluation of that same selected density on the finite
-- slow-field carrier.
--
-- This record makes the missing semantics typed:
--
--   weightOfDensity : Density -> SlowField -> Q.
--
-- The raw law at cutoff k is then definitionally
--
--   weightOfDensity (densityAt k).
--
-- No separately chosen probability weights are permitted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as CMP119
import DASHI.Physics.YangMills.BalabanFinitePositiveWeightNormalizationExact as Normalize
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact as Raw

record CMP119FiniteSlowDensityRealization
    {trajectory split}
    (source :
      CMP119.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs) : Set₁ where
  field
    scaleAt : Nat → Scale
    componentAt : Nat → Component

    slowStatesAt : Nat → List SlowField

    weightOfDensity :
      CMP119.Density source → SlowField → ℚ

    selectedDensityWeightNonnegative :
      ∀ cutoff slow →
      0ℚ ≤
      weightOfDensity
        (CMP119.densityAt source cutoff)
        slow

    positiveWitnessAt : Nat → SlowField

    positiveWitnessInStates : ∀ cutoff →
      PositiveMass._∈_
        (positiveWitnessAt cutoff)
        (slowStatesAt cutoff)

    positiveWitnessWeight : ∀ cutoff →
      Positive
        (weightOfDensity
          (CMP119.densityAt source cutoff)
          (positiveWitnessAt cutoff))

open CMP119FiniteSlowDensityRealization public

rawSelectedDensityWeights :
  ∀ {trajectory split source
      Scale Fine SlowField Component Functional construction
      referenceInputs typed} →
  CMP119FiniteSlowDensityRealization
    {trajectory = trajectory} {split = split}
    source
    {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
    {Component = Component} {Functional = Functional}
    {construction = construction}
    referenceInputs typed →
  Nat → Normalize.FinitePositiveWeightFamily SlowField
rawSelectedDensityWeights {source = source} realization cutoff = record
  { states = slowStatesAt realization cutoff
  ; rawWeight =
      weightOfDensity realization
        (CMP119.densityAt source cutoff)
  ; rawWeightNonnegative =
      selectedDensityWeightNonnegative realization cutoff
  ; positiveWitness =
      positiveWitnessAt realization cutoff
  ; positiveWitnessInStates =
      positiveWitnessInStates realization cutoff
  ; positiveWitnessWeight =
      positiveWitnessWeight realization cutoff
  }

compileSelectedDensityRawSlowLaw :
  ∀ {trajectory split source
      Scale Fine SlowField Component Functional construction
      referenceInputs typed}
    (realization :
      CMP119FiniteSlowDensityRealization
        {trajectory = trajectory} {split = split}
        source
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed) →
  Nat → Raw.Gate4RawSlowFieldDensity referenceInputs typed
compileSelectedDensityRawSlowLaw realization cutoff = record
  { scale = scaleAt realization cutoff
  ; component = componentAt realization cutoff
  ; rawSlowWeights =
      rawSelectedDensityWeights realization cutoff
  }

cmp119FiniteSlowDensityCompilerLevel : ProofLevel
cmp119FiniteSlowDensityCompilerLevel = machineChecked

cmp119SelectedDensityWeightFunctionLevel : ProofLevel
cmp119SelectedDensityWeightFunctionLevel = conditional

cmp119SelectedDensityWeightNonnegativeLevel : ProofLevel
cmp119SelectedDensityWeightNonnegativeLevel = conditional

cmp119SelectedDensityPositiveWitnessLevel : ProofLevel
cmp119SelectedDensityPositiveWitnessLevel = conditional
