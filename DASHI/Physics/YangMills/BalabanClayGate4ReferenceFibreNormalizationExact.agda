module DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibreNormalizationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
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

record FiniteReferenceFibreNormalization
    {Fine SlowField Scalar : Set}
    (sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar
    referenceSelector : Fine → Scalar
    suppression : Scalar

    multiplyZeroRight : ∀ value →
      multiply value (Integral.zero sumData) ≡ Integral.zero sumData
    distributeLeftOverAdd : ∀ coefficient left right →
      multiply coefficient (Integral.add sumData left right)
      ≡ Integral.add sumData
          (multiply coefficient left)
          (multiply coefficient right)

    referenceMassNormalized : ∀ slow fields →
      Integral.foldSelected sumData referenceSelector slow fields ≡ one
    suppressionTimesOne : multiply suppression one ≡ suppression

open FiniteReferenceFibreNormalization public

scaledSelector :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar} →
  FiniteReferenceFibreNormalization sumData → Fine → Scalar
scaledSelector normalization fine =
  multiply normalization (suppression normalization)
    (referenceSelector normalization fine)

scaleFiniteFold :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (normalization : FiniteReferenceFibreNormalization sumData)
    slow fields →
  Integral.foldSelected sumData (scaledSelector normalization) slow fields
  ≡ multiply normalization (suppression normalization)
      (Integral.foldSelected sumData
        (referenceSelector normalization) slow fields)
scaleFiniteFold normalization slow [] =
  sym (multiplyZeroRight normalization (suppression normalization))
scaleFiniteFold {sumData = sumData} normalization slow (fine ∷ fields) =
  trans
    (cong
      (Integral.add sumData
        (multiply normalization (suppression normalization)
          (referenceSelector normalization fine)))
      (scaleFiniteFold normalization slow fields))
    (sym (distributeLeftOverAdd normalization
      (suppression normalization)
      (referenceSelector normalization fine)
      (Integral.foldSelected sumData
        (referenceSelector normalization) slow fields)))

normalizedSuppressedReferenceFibreExact :
  ∀ {Fine SlowField Scalar}
    {sumData : Integral.FiniteConstrainedSum Fine SlowField Scalar}
    (normalization : FiniteReferenceFibreNormalization sumData)
    slow fields →
  Integral.foldSelected sumData (scaledSelector normalization) slow fields
  ≡ suppression normalization
normalizedSuppressedReferenceFibreExact normalization slow fields =
  trans
    (scaleFiniteFold normalization slow fields)
    (trans
      (cong (multiply normalization (suppression normalization))
        (referenceMassNormalized normalization slow fields))
      (suppressionTimesOne normalization))

record TReferenceFibreNormalization
    {Scale Fine SlowField Component Functional Scalar : Set}
    (dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar) : Set₁ where
  field
    normalization : FiniteReferenceFibreNormalization (T.sumData dataSet)
    referenceIntegrand : Scale → Component → SlowField → Fine → Scalar
    referenceIntegrandMeaning : ∀ scale component slow fine →
      referenceIntegrand scale component slow fine
      ≡ scaledSelector normalization fine

open TReferenceFibreNormalization public

referenceFibreAtFastFibreExact :
  ∀ {Scale Fine SlowField Component Functional Scalar}
    {dataSet : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional Scalar}
    (data : TReferenceFibreNormalization dataSet)
    scale component slow →
  Integral.foldSelected (T.sumData dataSet)
    (referenceIntegrand data scale component slow)
    slow (T.fastFibre dataSet scale component)
  ≡ suppression (normalization data)
referenceFibreAtFastFibreExact {dataSet = dataSet} data scale component slow =
  trans
    (foldCongruence
      (T.fastFibre dataSet scale component))
    (normalizedSuppressedReferenceFibreExact
      (normalization data) slow (T.fastFibre dataSet scale component))
  where
  foldCongruence : ∀ fields →
    Integral.foldSelected (T.sumData dataSet)
      (referenceIntegrand data scale component slow) slow fields
    ≡ Integral.foldSelected (T.sumData dataSet)
        (scaledSelector (normalization data)) slow fields
  foldCongruence [] = refl
  foldCongruence (fine ∷ fields) =
    cong₂ (Integral.add (T.sumData dataSet))
      (referenceIntegrandMeaning data scale component slow fine)
      (foldCongruence fields)
    where
    cong₂ : ∀ {A B C : Set} {a a' : A} {b b' : B} →
      (function : A → B → C) → a ≡ a' → b ≡ b' →
      function a b ≡ function a' b'
    cong₂ function refl refl = refl

finiteReferenceFibreScalingLevel : ProofLevel
finiteReferenceFibreScalingLevel = machineChecked

normalizedSuppressedReferenceFibreLevel : ProofLevel
normalizedSuppressedReferenceFibreLevel = machineChecked

tReferenceFibreAdapterLevel : ProofLevel
tReferenceFibreAdapterLevel = machineChecked

-- The remaining physical datum is the normalized Haar/Jacobian reference mass
-- on the selected fast fibre.  Once supplied, the suppression factor is pulled
-- through the finite integral by the theorem above; it is not a second estimate.
physicalReferenceHaarNormalizationInputsLevel : ProofLevel
physicalReferenceHaarNormalizationInputsLevel = conditional
