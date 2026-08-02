module DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteHolonomyGaugeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Dec)

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPhysicalAdjacencyAndBadReachExact as Physical

------------------------------------------------------------------------
-- Mathematical provenance.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, Springer (2015). DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I. The Basic Step of the R Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Hall owns the SU(2)/unit-quaternion group formula. Bałaban owns the lattice
-- gauge and large-field architecture. The rational polynomial identities and
-- periodic plaquette instance below are exact DASHI constructions.
------------------------------------------------------------------------

productReal productI productJ productK :
  Gap.RationalUnitQuaternion → Gap.RationalUnitQuaternion → ℚ
productReal left right =
  Gap.realPart left * Gap.realPart right
  - Gap.imagI left * Gap.imagI right
  - Gap.imagJ left * Gap.imagJ right
  - Gap.imagK left * Gap.imagK right
productI left right =
  Gap.realPart left * Gap.imagI right
  + Gap.imagI left * Gap.realPart right
  + Gap.imagJ left * Gap.imagK right
  - Gap.imagK left * Gap.imagJ right
productJ left right =
  Gap.realPart left * Gap.imagJ right
  - Gap.imagI left * Gap.imagK right
  + Gap.imagJ left * Gap.realPart right
  + Gap.imagK left * Gap.imagI right
productK left right =
  Gap.realPart left * Gap.imagK right
  + Gap.imagI left * Gap.imagJ right
  - Gap.imagJ left * Gap.imagI right
  + Gap.imagK left * Gap.realPart right

productNormSq :
  Gap.RationalUnitQuaternion → Gap.RationalUnitQuaternion → ℚ
productNormSq left right =
  productReal left right * productReal left right
  + productI left right * productI left right
  + productJ left right * productJ left right
  + productK left right * productK left right

productNormMultiplicative : ∀ (left right : Gap.RationalUnitQuaternion) →
  productNormSq left right
  ≡ Gap.quaternionNormSq left * Gap.quaternionNormSq right
productNormMultiplicative left right =
  regroup
    (Gap.realPart left) (Gap.imagI left) (Gap.imagJ left) (Gap.imagK left)
    (Gap.realPart right) (Gap.imagI right) (Gap.imagJ right) (Gap.imagK right)
  where
  regroup : (w1 x1 y1 z1 w2 x2 y2 z2 : ℚ) →
    (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) * (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2)
    + (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) * (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2)
    + (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) * (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2)
    + (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) * (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2)
    ≡ (w1 * w1 + x1 * x1 + y1 * y1 + z1 * z1) * (w2 * w2 + x2 * x2 + y2 * y2 + z2 * z2)
  regroup = ℚRing.solve-∀

productUnitNorm : ∀ (left right : Gap.RationalUnitQuaternion) → productNormSq left right ≡ 1ℚ
productUnitNorm left right =
  trans
    (productNormMultiplicative left right)
    (trans
      (cong₂ _*_
        (Gap.unitNormExact left)
        (Gap.unitNormExact right))
      (regroup))
  where
  regroup : 1ℚ * 1ℚ ≡ 1ℚ
  regroup = ℚRing.solve-∀

multiplyQuaternion :
  Gap.RationalUnitQuaternion → Gap.RationalUnitQuaternion →
  Gap.RationalUnitQuaternion
multiplyQuaternion left right = Gap.rationalUnitQuaternion
  (productReal left right)
  (productI left right)
  (productJ left right)
  (productK left right)
  (productUnitNorm left right)

inverseNormSq : Gap.RationalUnitQuaternion → ℚ
inverseNormSq value =
  Gap.realPart value * Gap.realPart value
  + (0ℚ - Gap.imagI value) * (0ℚ - Gap.imagI value)
  + (0ℚ - Gap.imagJ value) * (0ℚ - Gap.imagJ value)
  + (0ℚ - Gap.imagK value) * (0ℚ - Gap.imagK value)

inverseNormMatches : ∀ (value : Gap.RationalUnitQuaternion) →
  inverseNormSq value ≡ Gap.quaternionNormSq value
inverseNormMatches value =
  regroup (Gap.realPart value) (Gap.imagI value) (Gap.imagJ value) (Gap.imagK value)
  where
  regroup : (w x y zVal : ℚ) →
    w * w + (0ℚ - x) * (0ℚ - x) + (0ℚ - y) * (0ℚ - y) + (0ℚ - zVal) * (0ℚ - zVal)
    ≡ w * w + x * x + y * y + zVal * zVal
  regroup = ℚRing.solve-∀

inverseUnitNorm : ∀ (value : Gap.RationalUnitQuaternion) → inverseNormSq value ≡ 1ℚ
inverseUnitNorm value =
  trans (inverseNormMatches value) (Gap.unitNormExact value)

inverseQuaternion :
  Gap.RationalUnitQuaternion → Gap.RationalUnitQuaternion
inverseQuaternion value = Gap.rationalUnitQuaternion
  (Gap.realPart value)
  (0ℚ - Gap.imagI value)
  (0ℚ - Gap.imagJ value)
  (0ℚ - Gap.imagK value)
  (inverseUnitNorm value)

conjugateQuaternion :
  Gap.RationalUnitQuaternion → Gap.RationalUnitQuaternion →
  Gap.RationalUnitQuaternion
conjugateQuaternion gauge value =
  multiplyQuaternion
    (multiplyQuaternion gauge value)
    (inverseQuaternion gauge)

conjugationRealThroughGaugeNorm : ∀ (gauge value : Gap.RationalUnitQuaternion) →
  Gap.realPart (conjugateQuaternion gauge value)
  ≡ Gap.quaternionNormSq gauge * Gap.realPart value
conjugationRealThroughGaugeNorm gauge value =
  regroup
    (Gap.realPart gauge) (Gap.imagI gauge) (Gap.imagJ gauge) (Gap.imagK gauge)
    (Gap.realPart value) (Gap.imagI value) (Gap.imagJ value) (Gap.imagK value)
  where
  regroup : (w1 x1 y1 z1 w2 x2 y2 z2 : ℚ) →
    (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) * w1
    - (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) * (0ℚ - x1)
    - (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) * (0ℚ - y1)
    - (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) * (0ℚ - z1)
    ≡ (w1 * w1 + x1 * x1 + y1 * y1 + z1 * z1) * w2
  regroup = ℚRing.solve-∀

conjugationPreservesRealPart : ∀ (gauge value : Gap.RationalUnitQuaternion) →
  Gap.realPart (conjugateQuaternion gauge value)
  ≡ Gap.realPart value
conjugationPreservesRealPart gauge value =
  trans
    (conjugationRealThroughGaugeNorm gauge value)
    (trans
      (cong (λ normValue → normValue * Gap.realPart value)
        (Gap.unitNormExact gauge))
      (regroup (Gap.realPart value)))
  where
  regroup : (v : ℚ) → 1ℚ * v ≡ v
  regroup = ℚRing.solve-∀

conjugationPreservesTraceDeficit : ∀ (gauge value : Gap.RationalUnitQuaternion) →
  Gap.wilsonTraceDeficit (conjugateQuaternion gauge value)
  ≡ Gap.wilsonTraceDeficit value
conjugationPreservesTraceDeficit gauge value =
  cong (1ℚ -_) (conjugationPreservesRealPart gauge value)

conjugationPreservesChordalDistanceSq : ∀ (gauge value : Gap.RationalUnitQuaternion) →
  Gap.literalChordalDistanceSq (conjugateQuaternion gauge value)
  ≡ Gap.literalChordalDistanceSq value
conjugationPreservesChordalDistanceSq gauge value =
  trans
    (Gap.unitChordalEqualsTwiceTraceDeficit
      (conjugateQuaternion gauge value))
    (trans
      (cong (Gap.twoℚ *_)
        (conjugationPreservesTraceDeficit gauge value))
      (sym (Gap.unitChordalEqualsTwiceTraceDeficit value)))

------------------------------------------------------------------------
-- Literal periodic plaquette-holonomy field and local gauge action.
------------------------------------------------------------------------

PlaquetteHolonomyConfiguration : Nat → Set
PlaquetteHolonomyConfiguration n =
  Plaquette.PeriodicPlaquette n → Gap.RationalUnitQuaternion

PlaquetteGauge : Nat → Set
PlaquetteGauge n =
  Plaquette.PeriodicPlaquette n → Gap.RationalUnitQuaternion

transformPlaquetteConfiguration :
  ∀ {n} → PlaquetteGauge n → PlaquetteHolonomyConfiguration n →
  PlaquetteHolonomyConfiguration n
transformPlaquetteConfiguration gauge configuration plaquette =
  conjugateQuaternion (gauge plaquette) (configuration plaquette)

periodicPlaquetteDistanceGaugeInvariant :
  ∀ {n} (gauge : PlaquetteGauge n)
    (configuration : PlaquetteHolonomyConfiguration n) plaquette →
  Gap.literalChordalDistanceSq
    (transformPlaquetteConfiguration gauge configuration plaquette)
  ≡ Gap.literalChordalDistanceSq (configuration plaquette)
periodicPlaquetteDistanceGaugeInvariant gauge configuration plaquette =
  conjugationPreservesChordalDistanceSq
    (gauge plaquette) (configuration plaquette)

record LiteralPeriodicWilsonParameters
    (Scale : Set) : Set₁ where
  field
    coupling p0 threshold etaSquared scaleAdjustedThreshold : Scale → ℚ
    thresholdDefinition : ∀ scale →
      threshold scale ≡ coupling scale * p0 scale
    physicalThresholdBridge : ∀ scale →
      scaleAdjustedThreshold scale ≡ etaSquared scale * threshold scale
    lessEqualDecidable : ∀ (left right : ℚ) → Dec (left ≤ right)

open LiteralPeriodicWilsonParameters public

literalPeriodicPlaquetteWilsonData :
  ∀ {n Scale} → LiteralPeriodicWilsonParameters Scale →
  Wilson.LiteralWilsonLargeFieldData
    Scale
    (PlaquetteHolonomyConfiguration n)
    (PlaquetteGauge n)
    (Periodic.PeriodicBlock n)
    (Plaquette.PeriodicPlaquette n)
literalPeriodicPlaquetteWilsonData {n = n} parameters = record
  { transform = transformPlaquetteConfiguration
  ; Adjacent = Physical.PeriodicPhysicalAdjacent
  ; adjacentSymmetric = Physical.periodicPhysicalAdjacentSymmetric
  ; ownedPlaquettes = Plaquette.ownedPeriodicPlaquettes
  ; plaquetteHolonomy = λ configuration plaquette → configuration plaquette
  ; coupling = coupling parameters
  ; p0 = p0 parameters
  ; threshold = threshold parameters
  ; etaSquared = etaSquared parameters
  ; scaleAdjustedThreshold = scaleAdjustedThreshold parameters
  ; thresholdDefinition = thresholdDefinition parameters
  ; physicalThresholdBridge = physicalThresholdBridge parameters
  ; lessEqualDecidable = lessEqualDecidable parameters
  ; plaquetteDistanceGaugeInvariant = periodicPlaquetteDistanceGaugeInvariant
  }

rationalQuaternionMultiplicationLevel : ProofLevel
rationalQuaternionMultiplicationLevel = machineChecked

rationalQuaternionConjugationTraceLevel : ProofLevel
rationalQuaternionConjugationTraceLevel = machineChecked

plaquetteHolonomyGaugeInvarianceLevel : ProofLevel
plaquetteHolonomyGaugeInvarianceLevel = machineChecked

literalPeriodicWilsonDataInstanceLevel : ProofLevel
literalPeriodicWilsonDataInstanceLevel = machineChecked

-- Realizing this plaquette field as the boundary product of a periodic bond
-- field, and proving the corresponding local-site gauge-cancellation/Bianchi
-- identities, remains a distinct physical representation bridge.
periodicBondFieldHolonomyRealizationLevel : ProofLevel
periodicBondFieldHolonomyRealizationLevel = conditional
