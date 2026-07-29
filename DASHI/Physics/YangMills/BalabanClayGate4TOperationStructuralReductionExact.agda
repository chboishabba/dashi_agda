module DASHI.Physics.YangMills.BalabanClayGate4TOperationStructuralReductionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I. The Basic Step of the R Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- The remaining gauge/locality mathematics is representation-specific. This
-- module proves that pointwise equality of the selected finite-fibre integrands
-- is sufficient for equality of the concrete local T operation.
------------------------------------------------------------------------

foldSelectedCongruent :
  ∀ {Fine SlowField Scalar}
    (sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar)
    (fields : List Fine) (left right : Fine → Scalar)
    (leftCoarse rightCoarse : SlowField) →
  (∀ fine → left fine ≡ right fine) →
  Integral.foldSelected sumData left leftCoarse fields
  ≡ Integral.foldSelected sumData right rightCoarse fields
foldSelectedCongruent sumData [] left right leftCoarse rightCoarse pointwise = refl
foldSelectedCongruent sumData (fine ∷ fields) left right
  leftCoarse rightCoarse pointwise =
  cong₂ (Integral.add sumData)
    (pointwise fine)
    (foldSelectedCongruent sumData fields left right
      leftCoarse rightCoarse pointwise)

record TOperationPointwiseGaugeData
    {Scale Fine SlowField Component Functional Scalar Gauge : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    transformSlowField : Gauge → SlowField → SlowField
    transformFunctional : Gauge → Functional → Functional

    selectedIntegrandGaugeInvariant :
      ∀ (gauge : Gauge) (scale : Scale) (selectedComponent : Component)
        (slow : SlowField) (functional : Functional) (fine : Fine) →
      Integral.selectedWith (T.sumData dataSet)
        (T.localIntegrand dataSet scale selectedComponent
          (transformSlowField gauge slow)
          (transformFunctional gauge functional))
        (transformSlowField gauge slow) fine
      ≡ Integral.selectedWith (T.sumData dataSet)
          (T.localIntegrand dataSet scale selectedComponent slow functional)
          slow fine

open TOperationPointwiseGaugeData public

tOperationGaugeCovariantFromPointwiseFibre :
  ∀ {Scale Fine SlowField Component Functional Scalar Gauge}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (gaugeData : TOperationPointwiseGaugeData {Gauge = Gauge} dataSet)
    (gauge : Gauge) (scale : Scale)
    (selected : T.SecondClassComponent (T.classData dataSet) scale)
    (slow : SlowField) (functional : Functional) →
  T.localizedTOperation dataSet scale selected
    (transformSlowField gaugeData gauge slow)
    (transformFunctional gaugeData gauge functional)
  ≡ T.localizedTOperation dataSet scale selected slow functional
tOperationGaugeCovariantFromPointwiseFibre {dataSet = dataSet}
  gaugeData gauge scale selected slow functional =
  foldSelectedCongruent
    (T.sumData dataSet)
    (T.fastFibre dataSet scale (T.component selected))
    (Integral.selectedWith (T.sumData dataSet)
      (T.localIntegrand dataSet scale (T.component selected)
        (transformSlowField gaugeData gauge slow)
        (transformFunctional gaugeData gauge functional))
      (transformSlowField gaugeData gauge slow))
    (Integral.selectedWith (T.sumData dataSet)
      (T.localIntegrand dataSet scale (T.component selected) slow functional)
      slow)
    (transformSlowField gaugeData gauge slow)
    slow
    (selectedIntegrandGaugeInvariant gaugeData gauge scale
      (T.component selected) slow functional)

record TOperationPointwiseLocalityData
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    AgreeOnEnlargement : Scale → Component → SlowField → SlowField → Set

    selectedIntegrandDependsOnlyOnEnlargement :
      ∀ (scale : Scale) (selectedComponent : Component)
        (left right : SlowField) (functional : Functional) →
      AgreeOnEnlargement scale selectedComponent left right →
      ∀ fine →
      Integral.selectedWith (T.sumData dataSet)
        (T.localIntegrand dataSet scale selectedComponent left functional)
        left fine
      ≡ Integral.selectedWith (T.sumData dataSet)
          (T.localIntegrand dataSet scale selectedComponent right functional)
          right fine

open TOperationPointwiseLocalityData public

tOperationDependsOnlyOnEnlargementFromPointwiseFibre :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (localityData : TOperationPointwiseLocalityData dataSet)
    (scale : Scale)
    (selected : T.SecondClassComponent (T.classData dataSet) scale)
    (left right : SlowField) (functional : Functional) →
  AgreeOnEnlargement localityData scale (T.component selected) left right →
  T.localizedTOperation dataSet scale selected left functional
  ≡ T.localizedTOperation dataSet scale selected right functional
tOperationDependsOnlyOnEnlargementFromPointwiseFibre {dataSet = dataSet}
  localityData scale selected left right functional agreement =
  foldSelectedCongruent
    (T.sumData dataSet)
    (T.fastFibre dataSet scale (T.component selected))
    (Integral.selectedWith (T.sumData dataSet)
      (T.localIntegrand dataSet scale (T.component selected) left functional)
      left)
    (Integral.selectedWith (T.sumData dataSet)
      (T.localIntegrand dataSet scale (T.component selected) right functional)
      right)
    left
    right
    (selectedIntegrandDependsOnlyOnEnlargement localityData
      scale (T.component selected) left right functional agreement)

record TOperationDomainReduction
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    AdmissibleSlowField : Scale → SlowField → Set
    FineIntegrandDefined : Scale → Component → SlowField → Fine → Set

    everyFastFibreIntegrandDefined :
      ∀ (scale : Scale) (selectedComponent : Component) (slow : SlowField) →
      AdmissibleSlowField scale slow →
      ∀ fine → FineIntegrandDefined scale selectedComponent slow fine

open TOperationDomainReduction public

finiteTOperationFoldCongruenceLevel : ProofLevel
finiteTOperationFoldCongruenceLevel = machineChecked

tOperationGaugeCovarianceReductionLevel : ProofLevel
tOperationGaugeCovarianceReductionLevel = machineChecked

tOperationEnlargementLocalityReductionLevel : ProofLevel
tOperationEnlargementLocalityReductionLevel = machineChecked

tOperationPointwiseGaugeInvarianceInputsLevel : ProofLevel
tOperationPointwiseGaugeInvarianceInputsLevel = conditional

tOperationPointwiseEnlargementLocalityInputsLevel : ProofLevel
tOperationPointwiseEnlargementLocalityInputsLevel = conditional

tOperationFastFibreDomainInputsLevel : ProofLevel
tOperationFastFibreDomainInputsLevel = conditional
