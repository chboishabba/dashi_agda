module DASHI.Physics.YangMills.BalabanCMP119Gate4ConstrainedMassWeldExact where

------------------------------------------------------------------------
-- ASSEMBLED CMP119 DENSITY = GATE4 CONSTRAINED REFERENCE MASS
--
-- This is the sharp preferred finite source seam.
--
-- The physical/source payment is ONE same-object equality:
--
--   evaluate assembleDensity(T_k,A_k) at slow
--     =
--   constrained Gate4 reference mass at slow.
--
-- Once that equality is supplied, nonnegativity and strict positivity of the
-- selected raw slow-field weights are compiler output from the existing Gate4
-- constrained-reference theorem.  A selected slow-state list therefore needs
-- only one member witness; its positive weight is derived.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119AssembledFiniteSlowDensityExact as Assembled
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record CMP119Gate4ConstrainedMassWeld
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
    scaleAt : Nat → Scale
    componentAt : Nat → Component

    slowStatesAt : Nat → List SlowField
    slowWitnessAt : Nat → SlowField
    slowWitnessInStates : ∀ cutoff →
      PositiveMass._∈_ (slowWitnessAt cutoff) (slowStatesAt cutoff)

    assembledDensityIsConstrainedReferenceMass :
      ∀ cutoff slow →
      Assembled.assembledSelectedWeight evaluator cutoff slow
      ≡
      Kernel.constrainedReferenceMass
        referenceInputs
        (scaleAt cutoff)
        (componentAt cutoff)
        slow

open CMP119Gate4ConstrainedMassWeld public

selectedAssembledWeightNonnegative :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed evaluator}
    (weld :
      CMP119Gate4ConstrainedMassWeld
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed evaluator)
    cutoff slow →
  0ℚ ≤ Assembled.assembledSelectedWeight evaluator cutoff slow
selectedAssembledWeightNonnegative
  {referenceInputs = referenceInputs} {typed = typed}
  weld cutoff slow =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (assembledDensityIsConstrainedReferenceMass weld cutoff slow))
    (Kernel.constrainedReferenceMassNonnegative
      typed
      (scaleAt weld cutoff)
      (componentAt weld cutoff)
      slow)

selectedAssembledWeightPositive :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed evaluator}
    (weld :
      CMP119Gate4ConstrainedMassWeld
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed evaluator)
    cutoff slow →
  Positive (Assembled.assembledSelectedWeight evaluator cutoff slow)
selectedAssembledWeightPositive
  {referenceInputs = referenceInputs} {typed = typed}
  weld cutoff slow =
  subst
    Positive
    (sym (assembledDensityIsConstrainedReferenceMass weld cutoff slow))
    (Kernel.constrainedReferenceMassPositive
      typed
      (scaleAt weld cutoff)
      (componentAt weld cutoff)
      slow)

compileCMP119AssembledFiniteSlowDensityRealization :
  ∀ {trajectory split source family
      Scale Fine SlowField Component Functional construction
      referenceInputs typed evaluator}
    (weld :
      CMP119Gate4ConstrainedMassWeld
        {trajectory = trajectory} {split = split}
        source family
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        {construction = construction}
        referenceInputs typed evaluator) →
  Assembled.CMP119AssembledFiniteSlowDensityRealization
    source family referenceInputs typed evaluator
compileCMP119AssembledFiniteSlowDensityRealization weld = record
  { Assembled.CMP119AssembledFiniteSlowDensityRealization.scaleAt =
      scaleAt weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.componentAt =
      componentAt weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.slowStatesAt =
      slowStatesAt weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.selectedAssembledWeightNonnegative =
      selectedAssembledWeightNonnegative weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.positiveWitnessAt =
      slowWitnessAt weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.positiveWitnessInStates =
      slowWitnessInStates weld
  ; Assembled.CMP119AssembledFiniteSlowDensityRealization.positiveWitnessWeight =
      λ cutoff →
        selectedAssembledWeightPositive weld cutoff (slowWitnessAt weld cutoff)
  }

cmp119Gate4ConstrainedMassPositivityCompilerLevel : ProofLevel
cmp119Gate4ConstrainedMassPositivityCompilerLevel = machineChecked

cmp119Gate4ConstrainedMassSupportCompilerLevel : ProofLevel
cmp119Gate4ConstrainedMassSupportCompilerLevel = machineChecked

cmp119Gate4ConstrainedMassToFiniteSlowDensityCompilerLevel : ProofLevel
cmp119Gate4ConstrainedMassToFiniteSlowDensityCompilerLevel = machineChecked

-- Genuine source/representation theorem remaining on this route.
literalCMP119AssembledDensityIsGate4ConstrainedMassLevel : ProofLevel
literalCMP119AssembledDensityIsGate4ConstrainedMassLevel = conditional

-- Only combinatorial support remains after the weld: the selected slow-state
-- list must contain at least one state.
selectedSlowStateFamilyNonemptyLevel : ProofLevel
selectedSlowStateFamilyNonemptyLevel = conditional
