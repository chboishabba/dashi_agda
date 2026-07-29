module DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Project Euclid stable identifier: euclid:cmp/1104161193.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
------------------------------------------------------------------------

record FiniteReferenceFibreAlgebra
    {Fine SlowField Scalar : Set}
    (sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar

    multiplyZeroRight : ∀ value →
      multiply value (Integral.zero sumData) ≡ Integral.zero sumData
    distributeLeftOverAdd : ∀ coefficient left right →
      multiply coefficient (Integral.add sumData left right)
      ≡ Integral.add sumData
          (multiply coefficient left)
          (multiply coefficient right)
    multiplyOneRight : ∀ value → multiply value one ≡ value

open FiniteReferenceFibreAlgebra public

scaledSelector :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar} →
  FiniteReferenceFibreAlgebra sumData → Scalar →
  (Fine → Scalar) → Fine → Scalar
scaledSelector algebra coefficient selector fine =
  multiply algebra coefficient (selector fine)

scaleFiniteFold :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (algebra : FiniteReferenceFibreAlgebra sumData)
    coefficient selector slow fields →
  Integral.foldSelected sumData
    (scaledSelector algebra coefficient selector) slow fields
  ≡ multiply algebra coefficient
      (Integral.foldSelected sumData selector slow fields)
scaleFiniteFold algebra coefficient selector slow [] =
  sym (multiplyZeroRight algebra coefficient)
scaleFiniteFold {sumData = sumData} algebra coefficient selector slow
  (fine ∷ fields) =
  trans
    (cong
      (Integral.add sumData
        (multiply algebra coefficient (selector fine)))
      (scaleFiniteFold algebra coefficient selector slow fields))
    (sym (distributeLeftOverAdd algebra coefficient
      (selector fine)
      (Integral.foldSelected sumData selector slow fields)))

record ReciprocalReferenceMass
    {Fine SlowField Scalar : Set}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (algebra : FiniteReferenceFibreAlgebra sumData)
    (selector : Fine → Scalar) (slow : SlowField) (fields : List Fine) : Set₁ where
  field
    mass reciprocalMass : Scalar
    massDefinition :
      Integral.foldSelected sumData selector slow fields ≡ mass
    reciprocalTimesMass :
      multiply algebra reciprocalMass mass ≡ one algebra

open ReciprocalReferenceMass public

normalizedReferenceSelector :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    {algebra : FiniteReferenceFibreAlgebra sumData}
    {selector : Fine → Scalar} {slow fields} →
  ReciprocalReferenceMass algebra selector slow fields → Fine → Scalar
normalizedReferenceSelector {algebra = algebra} {selector = selector} reciprocal =
  scaledSelector algebra (reciprocalMass reciprocal) selector

normalizedReferenceMassExact :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    {algebra : FiniteReferenceFibreAlgebra sumData}
    {selector : Fine → Scalar} {slow fields}
    (reciprocal : ReciprocalReferenceMass algebra selector slow fields) →
  Integral.foldSelected sumData
    (normalizedReferenceSelector reciprocal) slow fields
  ≡ one algebra
normalizedReferenceMassExact {algebra = algebra} {selector = selector}
  {slow = slow} {fields = fields} reciprocal =
  trans
    (scaleFiniteFold algebra (reciprocalMass reciprocal) selector slow fields)
    (trans
      (cong (multiply algebra (reciprocalMass reciprocal))
        (massDefinition reciprocal))
      (reciprocalTimesMass reciprocal))

normalizedSuppressedReferenceFibreExact :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (algebra : FiniteReferenceFibreAlgebra sumData)
    suppression selector slow fields →
  Integral.foldSelected sumData selector slow fields ≡ one algebra →
  Integral.foldSelected sumData
    (scaledSelector algebra suppression selector) slow fields
  ≡ suppression
normalizedSuppressedReferenceFibreExact algebra suppression selector slow fields
  normalized =
  trans
    (scaleFiniteFold algebra suppression selector slow fields)
    (trans
      (cong (multiply algebra suppression) normalized)
      (multiplyOneRight algebra suppression))

record TReferenceFibreNormalization
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    algebra : FiniteReferenceFibreAlgebra (T.sumData dataSet)
    referenceSelector : Scale → Component → SlowField → Fine → Scalar
    suppression : Scale → Scalar

    referenceMassNormalizedOnFastFibre :
      ∀ scale component slow →
      Integral.foldSelected (T.sumData dataSet)
        (referenceSelector scale component slow)
        slow (T.fastFibre dataSet scale component)
      ≡ one algebra

open TReferenceFibreNormalization public

referenceIntegrand :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar} →
  TReferenceFibreNormalization dataSet →
  Scale → Component → SlowField → Fine → Scalar
referenceIntegrand data scale component slow =
  scaledSelector (algebra data) (suppression data scale)
    (referenceSelector data scale component slow)

referenceFibreAtFastFibreExact :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (data : TReferenceFibreNormalization dataSet)
    scale component slow →
  Integral.foldSelected (T.sumData dataSet)
    (referenceIntegrand data scale component slow)
    slow (T.fastFibre dataSet scale component)
  ≡ suppression data scale
referenceFibreAtFastFibreExact {dataSet = dataSet} data scale component slow =
  normalizedSuppressedReferenceFibreExact
    (algebra data)
    (suppression data scale)
    (referenceSelector data scale component slow)
    slow
    (T.fastFibre dataSet scale component)
    (referenceMassNormalizedOnFastFibre data scale component slow)

finiteReferenceFibreScalingLevel : ProofLevel
finiteReferenceFibreScalingLevel = machineChecked

reciprocalReferenceNormalizationLevel : ProofLevel
reciprocalReferenceNormalizationLevel = machineChecked

normalizedSuppressedReferenceFibreLevel : ProofLevel
normalizedSuppressedReferenceFibreLevel = machineChecked

tReferenceFibreAdapterLevel : ProofLevel
tReferenceFibreAdapterLevel = machineChecked

physicalReferenceMassNonzeroReciprocalInputsLevel : ProofLevel
physicalReferenceMassNonzeroReciprocalInputsLevel = conditional
