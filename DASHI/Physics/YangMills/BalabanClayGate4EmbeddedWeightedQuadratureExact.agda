module DASHI.Physics.YangMills.BalabanClayGate4EmbeddedWeightedQuadratureExact where

------------------------------------------------------------------------
-- REAL-WEIGHTED GATE4 QUADRATURE
--
-- The canonical rational Gate4 T-operation is an unweighted finite fold.
-- A literal Haar tagged quadrature needs one additional factor per selected
-- fine configuration: the Haar mass of its cell.
--
-- This owner keeps the physical Gate4 one-integrand unchanged and multiplies
-- its rational real image by an explicit real quadrature mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as AddEmbed
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as BaseEmbed
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactTaggedPartitionExact as Tagged
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as Error

embedQ :
  RingEmbed.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  BaseEmbed.embed
    (AddEmbed.base (RingEmbed.additive embedding))

record EmbeddedWeightedGate4Quadrature
    {Scale Fine SlowField Component Functional : Set}
    (construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional)
    (embedding : RingEmbed.RationalRealRingEmbedding) : Set₁ where
  field
    quadratureMass :
      Scale → Component → SlowField → Fine → ℝ

open EmbeddedWeightedGate4Quadrature public

embeddedSelectedOneIntegrand :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (embedding : RingEmbed.RationalRealRingEmbedding) →
  Scale → Component → SlowField → Fine → ℝ
embeddedSelectedOneIntegrand
  {construction = construction} embedding scale component slow fine =
  embedQ embedding
    (Integral.selectedWith
      (T.sumData (PhysicalT.canonicalPhysicalTData construction))
      (T.localIntegrand
        (PhysicalT.canonicalPhysicalTData construction)
        scale component slow
        (T.oneFunctional
          (PhysicalT.canonicalPhysicalTData construction)))
      slow fine)

weightedSelectedOneIntegrand :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {embedding : RingEmbed.RationalRealRingEmbedding} →
  EmbeddedWeightedGate4Quadrature construction embedding →
  Scale → Component → SlowField → Fine → ℝ
weightedSelectedOneIntegrand
  {embedding = embedding} dataSet scale component slow fine =
  quadratureMass dataSet scale component slow fine
    *ℝ
  embeddedSelectedOneIntegrand embedding scale component slow fine

weightedGate4Quadrature :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {embedding : RingEmbed.RationalRealRingEmbedding} →
  EmbeddedWeightedGate4Quadrature construction embedding →
  (scale : Scale) →
  T.SecondClassComponent
    (T.classData (PhysicalT.canonicalPhysicalTData construction))
    scale →
  SlowField → ℝ
weightedGate4Quadrature
  {construction = construction}
  dataSet scale selected slow =
  RingEmbed.realSum
    (T.fastFibre
      (PhysicalT.canonicalPhysicalTData construction)
      scale
      (T.component selected))
    (weightedSelectedOneIntegrand
      dataSet scale (T.component selected) slow)

record MassExactTaggedGate4Realization
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (weighted :
      EmbeddedWeightedGate4Quadrature construction embedding)
    (scale : Scale)
    (selected :
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        scale)
    (slow : SlowField)
    (tagged : Tagged.MassExactTaggedPartition Fine) : Set₁ where
  field
    cellsAreFastFibre :
      Tagged.cells tagged
      ≡
      T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        scale
        (T.component selected)

    cellMassIsQuadratureMass :
      ∀ fine →
      Tagged.cellMass tagged fine
      ≡ quadratureMass weighted
          scale (T.component selected) slow fine

    sampleIsEmbeddedSelectedOneIntegrand :
      ∀ fine →
      Tagged.sampleValue tagged fine
      ≡ embeddedSelectedOneIntegrand embedding
          scale (T.component selected) slow fine

open MassExactTaggedGate4Realization public

taggedQuadratureTermIsWeightedGate4Term :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {weighted :
      EmbeddedWeightedGate4Quadrature construction embedding}
    {scale}
    {selected :
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        scale}
    {slow}
    {tagged : Tagged.MassExactTaggedPartition Fine}
    (realization :
      MassExactTaggedGate4Realization
        weighted scale selected slow tagged)
    fine →
  Error.quadratureCellValue
    (Tagged.asFiniteQuadratureCellError tagged)
    fine
  ≡
  weightedSelectedOneIntegrand
    weighted scale (T.component selected) slow fine
taggedQuadratureTermIsWeightedGate4Term
  {weighted = weighted} {scale = scale}
  {selected = selected} {slow = slow} {tagged = tagged}
  realization fine =
  trans
    (cong
      (λ massValue →
        massValue *ℝ Tagged.sampleValue tagged fine)
      (cellMassIsQuadratureMass realization fine))
    (cong
      (λ sampleValue →
        quadratureMass weighted
          scale (T.component selected) slow fine
          *ℝ sampleValue)
      (sampleIsEmbeddedSelectedOneIntegrand realization fine))

taggedQuadratureIsWeightedGate4Quadrature :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    {weighted :
      EmbeddedWeightedGate4Quadrature construction embedding}
    {scale}
    {selected :
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        scale}
    {slow}
    {tagged : Tagged.MassExactTaggedPartition Fine}
    (realization :
      MassExactTaggedGate4Realization
        weighted scale selected slow tagged) →
  Tagged.taggedQuadratureSum tagged
  ≡
  weightedGate4Quadrature weighted scale selected slow
taggedQuadratureIsWeightedGate4Quadrature
  {construction = construction}
  {weighted = weighted} {scale = scale}
  {selected = selected} {slow = slow} {tagged = tagged}
  realization =
  subst
    (λ fields →
      RingEmbed.realSum fields
        (Error.quadratureCellValue
          (Tagged.asFiniteQuadratureCellError tagged))
      ≡
      weightedGate4Quadrature weighted scale selected slow)
    (sym (cellsAreFastFibre realization))
    (RingEmbed.realSumCong
      (T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        scale (T.component selected))
      (taggedQuadratureTermIsWeightedGate4Term realization))

embeddedWeightedGate4QuadratureLevel : ProofLevel
embeddedWeightedGate4QuadratureLevel = machineChecked

massExactTaggedGate4CompilerLevel : ProofLevel
massExactTaggedGate4CompilerLevel = machineChecked

-- Source/geometry payments now become explicit:
-- * choose quadratureMass as literal Haar cell mass;
-- * identify tagged cells with the selected Gate4 fast fibre;
-- * prove the source Eq.(1.71) value at each tag is the embedded Gate4
--   selected one-integrand.
literalGate4QuadratureMassIsHaarCellMassLevel : ProofLevel
literalGate4QuadratureMassIsHaarCellMassLevel = conditional

literalGate4FastFibreIsTaggedProductSU2Level : ProofLevel
literalGate4FastFibreIsTaggedProductSU2Level = conditional

literalEquation171TagValueIsGate4OneIntegrandLevel : ProofLevel
literalEquation171TagValueIsGate4OneIntegrandLevel = conditional
