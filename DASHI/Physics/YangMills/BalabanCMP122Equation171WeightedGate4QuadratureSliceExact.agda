module DASHI.Physics.YangMills.BalabanCMP122Equation171WeightedGate4QuadratureSliceExact where

------------------------------------------------------------------------
-- SOURCE-FAITHFUL EQ.(1.71) MASS-EXACT WEIGHTED GATE4 SLICE
--
-- One refinement/cutoff/background slice carries:
--
--   * literal source/Haar cell integrals and exact cell masses;
--   * the same selected fine tags as Gate4;
--   * source tag value = embedded Gate4 selected one-integrand;
--   * quadrature mass = source/Haar cell mass.
--
-- Hence the tagged quadrature is definitionally/compiler equal to the
-- REAL-WEIGHTED Gate4 quadrature.  No equality with the legacy unweighted
-- rational T-operation is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact as Tagged
import DASHI.Physics.YangMills.BalabanClayGate4EmbeddedWeightedQuadratureExact as Weighted

record Equation171WeightedGate4QuadratureSlice
    {Scale Fine SlowField Component Functional : Set}
    (construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional)
    (source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding) : Set₂ where
  field
    weighted :
      Weighted.EmbeddedWeightedGate4Quadrature
        construction embedding

    scaleAt : Nat → Scale

    selectedAt : ∀ cutoff →
      T.SecondClassComponent
        (T.classData
          (PhysicalT.canonicalPhysicalTData construction))
        (scaleAt cutoff)

    taggedAt : ∀ cutoff slow →
      Tagged.MassExactTaggedPartition Fine

    taggedGate4Realization : ∀ cutoff slow →
      Weighted.MassExactTaggedGate4Realization
        weighted
        (scaleAt cutoff)
        (selectedAt cutoff)
        slow
        (taggedAt cutoff slow)

    -- Literal Eq.(1.71) cell decomposition on these same cells.
    sourcePartitionIsEquation171Integral :
      ∀ cutoff slow →
      Tagged.taggedSourceIntegral
        (taggedAt cutoff slow)
      ≡
      Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow)

    -- Pointwise source identification.  This is G3 on the actual tags.
    sourceTagValueIsEquation171Density :
      ∀ cutoff slow fine →
      Tagged.sampleValue (taggedAt cutoff slow) fine
      ≡
      Eq171.equation171ExponentialDensity
        source cutoff slow fine

open Equation171WeightedGate4QuadratureSlice public

taggedQuadratureIsWeightedGate4 :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (slice :
      Equation171WeightedGate4QuadratureSlice
        construction source embedding)
    cutoff slow →
  Tagged.taggedQuadratureSum
    (taggedAt slice cutoff slow)
  ≡
  Weighted.weightedGate4Quadrature
    (weighted slice)
    (scaleAt slice cutoff)
    (selectedAt slice cutoff)
    slow
taggedQuadratureIsWeightedGate4 slice cutoff slow =
  Weighted.taggedQuadratureIsWeightedGate4Quadrature
    (taggedGate4Realization slice cutoff slow)

sourceTagDensityIsEmbeddedGate4 :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (slice :
      Equation171WeightedGate4QuadratureSlice
        construction source embedding)
    cutoff slow fine →
  Eq171.equation171ExponentialDensity source cutoff slow fine
  ≡
  Weighted.embeddedSelectedOneIntegrand embedding
    (scaleAt slice cutoff)
    (T.component (selectedAt slice cutoff))
    slow fine
sourceTagDensityIsEmbeddedGate4 slice cutoff slow fine =
  trans
    (Relation.Binary.PropositionalEquality.sym
      (sourceTagValueIsEquation171Density
        slice cutoff slow fine))
    (Weighted.sampleIsEmbeddedSelectedOneIntegrand
      (taggedGate4Realization slice cutoff slow)
      fine)
  where
  import Relation.Binary.PropositionalEquality

weightedEquation171SliceCompilerLevel : ProofLevel
weightedEquation171SliceCompilerLevel = machineChecked

weightedEquation171TaggedQuadratureCompilerLevel : ProofLevel
weightedEquation171TaggedQuadratureCompilerLevel = machineChecked

-- True source/geometry leaves:
literalEquation171WeightedSourcePartitionLevel : ProofLevel
literalEquation171WeightedSourcePartitionLevel = conditional

literalEquation171WeightedTagDensityLevel : ProofLevel
literalEquation171WeightedTagDensityLevel = conditional

literalEquation171WeightedFastFibreTagsLevel : ProofLevel
literalEquation171WeightedFastFibreTagsLevel = conditional

literalEquation171WeightedHaarMassLevel : ProofLevel
literalEquation171WeightedHaarMassLevel = conditional
