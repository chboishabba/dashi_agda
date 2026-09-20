module DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4QuadratureSliceExact where

------------------------------------------------------------------------
-- ONE GATE4 QUADRATURE SLICE FOR CMP122 EQ.(1.71)
--
-- A refinement slice pays only representation/pointwise obligations:
--
--   G1 fibre
--   G2 coarse selector
--   G3/G5 source exponential density = embedded Gate4 one-integrand
--
-- It does NOT claim that one finite slice equals the literal Haar integral.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as AddEmbed
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as BaseEmbed
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanEmbeddedCanonicalRationalConstrainedFoldExact as Embedded

embedQ :
  RingEmbed.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  BaseEmbed.embed
    (AddEmbed.base (RingEmbed.additive embedding))

record Equation171Gate4QuadratureSlice
    {Scale Fine SlowField Component Functional : Set}
    (construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional)
    (source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding) : Set₁ where
  field
    scaleAt : Nat → Scale

    selectedAt : ∀ cutoff →
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        (scaleAt cutoff)

    sourceFibre :
      Nat → SlowField → List Fine

    fibreIsGate4FastFibre :
      ∀ cutoff slow →
      sourceFibre cutoff slow
      ≡
      T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt cutoff)
        (T.component (selectedAt cutoff))

    sourceCoarseMatches :
      Nat → Fine → SlowField → Bool

    sourceCoarseMatchesIsGate4 :
      ∀ cutoff fine slow →
      sourceCoarseMatches cutoff fine slow
      ≡
      Integral.coarseMatches
        (T.sumData (PhysicalT.canonicalPhysicalTData construction))
        fine slow

    sourceSelectedIntegrand :
      Nat → SlowField → Fine → ℝ

    sourceSelectedWhenTrue :
      ∀ cutoff slow fine →
      sourceCoarseMatches cutoff fine slow ≡ true →
      sourceSelectedIntegrand cutoff slow fine
      ≡ Eq171.equation171ExponentialDensity source cutoff slow fine

    sourceSelectedWhenFalse :
      ∀ cutoff slow fine →
      sourceCoarseMatches cutoff fine slow ≡ false →
      sourceSelectedIntegrand cutoff slow fine ≡ 0ℝ

    exponentialDensityIsEmbeddedGate4OneIntegrand :
      ∀ cutoff slow fine →
      Eq171.equation171ExponentialDensity source cutoff slow fine
      ≡
      embedQ embedding
        (T.localIntegrand
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt cutoff)
          (T.component (selectedAt cutoff))
          slow
          (T.oneFunctional
            (PhysicalT.canonicalPhysicalTData construction))
          fine)

open Equation171Gate4QuadratureSlice public

sourceSelectedIntegrandIsEmbeddedGate4Selected :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (slice :
      Equation171Gate4QuadratureSlice construction source embedding)
    cutoff slow fine →
  sourceSelectedIntegrand slice cutoff slow fine
  ≡
  embedQ embedding
    (Integral.selectedWith
      (T.sumData (PhysicalT.canonicalPhysicalTData construction))
      (T.localIntegrand
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt slice cutoff)
        (T.component (selectedAt slice cutoff))
        slow
        (T.oneFunctional
          (PhysicalT.canonicalPhysicalTData construction)))
      slow fine)
sourceSelectedIntegrandIsEmbeddedGate4Selected
  {construction = construction} {embedding = embedding}
  slice cutoff slow fine
  with sourceCoarseMatches slice cutoff fine slow
     | Integral.coarseMatches
         (T.sumData (PhysicalT.canonicalPhysicalTData construction))
         fine slow
     | sourceCoarseMatchesIsGate4 slice cutoff fine slow
... | true | true | refl =
  trans
    (sourceSelectedWhenTrue slice cutoff slow fine refl)
    (exponentialDensityIsEmbeddedGate4OneIntegrand
      slice cutoff slow fine)
... | false | false | refl =
  trans
    (sourceSelectedWhenFalse slice cutoff slow fine refl)
    (sym
      (BaseEmbed.zeroExact
        (AddEmbed.base (RingEmbed.additive embedding))))

sourceFiniteFold :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding} →
  Equation171Gate4QuadratureSlice construction source embedding →
  Nat → SlowField → ℝ
sourceFiniteFold slice cutoff slow =
  RingEmbed.realSum
    (sourceFibre slice cutoff slow)
    (sourceSelectedIntegrand slice cutoff slow)

embeddedGate4Mass :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding} →
  Equation171Gate4QuadratureSlice construction source embedding →
  Nat → SlowField → ℝ
embeddedGate4Mass
  {construction = construction} {embedding = embedding}
  slice cutoff slow =
  embedQ embedding
    (T.localizedTOperation
      (PhysicalT.canonicalPhysicalTData construction)
      (scaleAt slice cutoff)
      (selectedAt slice cutoff)
      slow
      (T.oneFunctional
        (PhysicalT.canonicalPhysicalTData construction)))

sourceFiniteFoldIsEmbeddedGate4Mass :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (slice :
      Equation171Gate4QuadratureSlice construction source embedding)
    cutoff slow →
  sourceFiniteFold slice cutoff slow
  ≡ embeddedGate4Mass slice cutoff slow
sourceFiniteFoldIsEmbeddedGate4Mass
  {construction = construction} {embedding = embedding}
  slice cutoff slow
  rewrite fibreIsGate4FastFibre slice cutoff slow =
  trans
    (RingEmbed.realSumCong
      (T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt slice cutoff)
        (T.component (selectedAt slice cutoff)))
      (sourceSelectedIntegrandIsEmbeddedGate4Selected
        slice cutoff slow))
    (sym
      (Embedded.embeddedConstrainedIntegralExact
        embedding
        (PhysicalT.sumCarrier construction)
        (T.fastFibre
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt slice cutoff)
          (T.component (selectedAt slice cutoff)))
        (T.localIntegrand
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt slice cutoff)
          (T.component (selectedAt slice cutoff))
          slow
          (T.oneFunctional
            (PhysicalT.canonicalPhysicalTData construction)))
        slow))

equation171Gate4QuadratureSliceCompilerLevel : ProofLevel
equation171Gate4QuadratureSliceCompilerLevel = machineChecked

equation171Gate4SliceFoldCompilerLevel : ProofLevel
equation171Gate4SliceFoldCompilerLevel = machineChecked

literalEquation171SliceFibreLevel : ProofLevel
literalEquation171SliceFibreLevel = conditional

literalEquation171SliceSelectorLevel : ProofLevel
literalEquation171SliceSelectorLevel = conditional

literalEquation171SliceIntegrandLevel : ProofLevel
literalEquation171SliceIntegrandLevel = conditional

literalEquation171SliceMeasureFactorsLevel : ProofLevel
literalEquation171SliceMeasureFactorsLevel = conditional
