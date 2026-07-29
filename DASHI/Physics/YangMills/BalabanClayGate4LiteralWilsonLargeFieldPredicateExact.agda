module DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Empty; Dec; yes; no)

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact as Geometry

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I. The Basic Step of the
-- R Operation", Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Communications in
-- Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Relationship: the two 1985 papers own the gauge-covariant averaging and
-- constrained-background lanes; the 1989 pair owns the large-field/R-operation
-- architecture. The concrete SU(2) trace/chordal identity and rational Wilson
-- cost reduction are reused from BalabanSU2RationalWilsonLargeFieldGapExact.
-- The February 2026 Eriksson viXra paper is only a locator for notation and is
-- not admitted as theorem authority.
------------------------------------------------------------------------

data _∈_ {A : Set} (value : A) : List A → Set where
  here  : ∀ {values} → value ∈ (value ∷ values)
  there : ∀ {other values} → value ∈ values → value ∈ (other ∷ values)

record LiteralWilsonLargeFieldData
    (Scale Configuration Gauge Block Plaquette : Set) : Set₁ where
  field
    transform : Gauge → Configuration → Configuration
    Adjacent : Block → Block → Set
    adjacentSymmetric : ∀ {left right} →
      Adjacent left right → Adjacent right left

    ownedPlaquettes : Block → List Plaquette
    plaquetteHolonomy : Configuration → Plaquette → Gap.RationalUnitQuaternion

    coupling p0 threshold etaSquared scaleAdjustedThreshold : Scale → ℚ
    thresholdDefinition : ∀ scale →
      threshold scale ≡ coupling scale * p0 scale

    -- The locator uses both epsilon_k and epsilon_k eta^2. This bridge remains
    -- explicit until the primary scale convention is fixed.
    physicalThresholdBridge : ∀ scale →
      scaleAdjustedThreshold scale ≡ etaSquared scale * threshold scale

    lessEqualDecidable : ∀ left right → Dec (left ≤ right)

    plaquetteDistanceGaugeInvariant : ∀ gauge configuration plaquette →
      Gap.literalChordalDistanceSq
        (plaquetteHolonomy (transform gauge configuration) plaquette)
      ≡
      Gap.literalChordalDistanceSq
        (plaquetteHolonomy configuration plaquette)

open LiteralWilsonLargeFieldData public

LargePlaquette :
  ∀ {Scale Configuration Gauge Block Plaquette} →
  LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette →
  Scale → Configuration → Plaquette → Set
LargePlaquette dataSet scale configuration plaquette =
  Gap.squareℚ (threshold dataSet scale)
  ≤ Gap.literalChordalDistanceSq
      (plaquetteHolonomy dataSet configuration plaquette)

data LargeFieldBlock
    {Scale Configuration Gauge Block Plaquette : Set}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    (scale : Scale) (configuration : Configuration) (block : Block) : Set where
  largeWitness : ∀ plaquette →
    plaquette ∈ ownedPlaquettes dataSet block →
    LargePlaquette dataSet scale configuration plaquette →
    LargeFieldBlock dataSet scale configuration block

largePlaquetteDecidable :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    scale configuration plaquette →
  Dec (LargePlaquette dataSet scale configuration plaquette)
largePlaquetteDecidable dataSet scale configuration plaquette =
  lessEqualDecidable dataSet
    (Gap.squareℚ (threshold dataSet scale))
    (Gap.literalChordalDistanceSq
      (plaquetteHolonomy dataSet configuration plaquette))

anyLargeOwnedPlaquette :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    scale configuration block
    (plaquettes : List Plaquette) →
  Dec (LargeFieldBlock dataSet scale configuration block)
anyLargeOwnedPlaquette dataSet scale configuration block [] =
  no (λ ())
anyLargeOwnedPlaquette dataSet scale configuration block (plaquette ∷ plaquettes)
  with largePlaquetteDecidable dataSet scale configuration plaquette
... | yes large = yes (largeWitness plaquette here large)
... | no notLarge
  with anyLargeOwnedPlaquette dataSet scale configuration block plaquettes
... | yes (largeWitness witness member large) =
      yes (largeWitness witness (there member) large)
... | no noTail = no reject
  where
  reject : LargeFieldBlock dataSet scale configuration block → Empty
  reject (largeWitness .plaquette here large) = notLarge large
  reject (largeWitness witness (there member) large) =
    noTail (largeWitness witness member large)

largeFieldBlockDecidable :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    scale configuration block →
  Dec (LargeFieldBlock dataSet scale configuration block)
largeFieldBlockDecidable dataSet scale configuration block =
  anyLargeOwnedPlaquette dataSet scale configuration block
    (ownedPlaquettes dataSet block)

largePlaquetteGaugeForward :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    gauge scale configuration plaquette →
  LargePlaquette dataSet scale configuration plaquette →
  LargePlaquette dataSet scale (transform dataSet gauge configuration) plaquette
largePlaquetteGaugeForward dataSet gauge scale configuration plaquette large =
  subst
    (λ right → Gap.squareℚ (threshold dataSet scale) ≤ right)
    (sym (plaquetteDistanceGaugeInvariant dataSet gauge configuration plaquette))
    large

largePlaquetteGaugeBackward :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    gauge scale configuration plaquette →
  LargePlaquette dataSet scale (transform dataSet gauge configuration) plaquette →
  LargePlaquette dataSet scale configuration plaquette
largePlaquetteGaugeBackward dataSet gauge scale configuration plaquette large =
  subst
    (λ right → Gap.squareℚ (threshold dataSet scale) ≤ right)
    (plaquetteDistanceGaugeInvariant dataSet gauge configuration plaquette)
    large

largeFieldBlockGaugeForward :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    gauge scale configuration block →
  LargeFieldBlock dataSet scale configuration block →
  LargeFieldBlock dataSet scale (transform dataSet gauge configuration) block
largeFieldBlockGaugeForward dataSet gauge scale configuration block
  (largeWitness plaquette member large) =
  largeWitness plaquette member
    (largePlaquetteGaugeForward dataSet gauge scale configuration plaquette large)

largeFieldBlockGaugeBackward :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    gauge scale configuration block →
  LargeFieldBlock dataSet scale (transform dataSet gauge configuration) block →
  LargeFieldBlock dataSet scale configuration block
largeFieldBlockGaugeBackward dataSet gauge scale configuration block
  (largeWitness plaquette member large) =
  largeWitness plaquette member
    (largePlaquetteGaugeBackward dataSet gauge scale configuration plaquette large)

literalWilsonBadBlockGeometry :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    (scale : Scale) →
  Geometry.BadBlockGeometry Configuration Gauge Block
literalWilsonBadBlockGeometry dataSet scale = record
  { transform = transform dataSet
  ; Adjacent = Adjacent dataSet
  ; adjacentSymmetric = adjacentSymmetric dataSet
  ; BadBlock = λ configuration block →
      LargeFieldBlock dataSet scale configuration block
  ; badBlockDecidable = largeFieldBlockDecidable dataSet scale
  ; badGaugeForward = λ gauge configuration block →
      largeFieldBlockGaugeForward dataSet gauge scale configuration block
  ; badGaugeBackward = λ gauge configuration block →
      largeFieldBlockGaugeBackward dataSet gauge scale configuration block
  }

------------------------------------------------------------------------
-- Exact local Wilson cost bridge, reusing the existing SU(2) theorem.
------------------------------------------------------------------------

record LiteralWilsonCostData
    {Scale Configuration Gauge Block Plaquette : Set}
    (largeField : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette) : Set₁ where
  field
    beta : Scale → ℚ
    order : Gap.RationalWilsonGapOrder
    halfBetaNonnegative : ∀ scale → 0ℚ ≤ Gap.halfℚ * beta scale

open LiteralWilsonCostData public

scaledWilsonPlaquetteCost :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette} →
  LiteralWilsonCostData largeField → Scale → Configuration → Plaquette → ℚ
scaledWilsonPlaquetteCost {largeField = largeField}
  cost scale configuration plaquette =
  Gap.wilsonPlaquetteAction (beta cost scale)
    (plaquetteHolonomy largeField configuration plaquette)

largePlaquetteImpliesWilsonCost :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    (cost : LiteralWilsonCostData largeField)
    scale configuration plaquette →
  LargePlaquette largeField scale configuration plaquette →
  (Gap.halfℚ * beta cost scale)
    * Gap.squareℚ (threshold largeField scale)
  ≤ scaledWilsonPlaquetteCost cost scale configuration plaquette
largePlaquetteImpliesWilsonCost {largeField = largeField}
  cost scale configuration plaquette large =
  Gap.localWilsonActionGap
    (order cost)
    (beta cost scale)
    (threshold largeField scale)
    (plaquetteHolonomy largeField configuration plaquette)
    (halfBetaNonnegative cost scale)
    large

literalWilsonPredicateDefinitionLevel : ProofLevel
literalWilsonPredicateDefinitionLevel = machineChecked

literalWilsonBadBlockDecidabilityLevel : ProofLevel
literalWilsonBadBlockDecidabilityLevel = machineChecked

literalWilsonGaugeInvariantBadComponentInstanceLevel : ProofLevel
literalWilsonGaugeInvariantBadComponentInstanceLevel = machineChecked

literalSU2ThresholdToWilsonCostLevel : ProofLevel
literalSU2ThresholdToWilsonCostLevel = machineChecked

literalScaleAdjustedThresholdBridgeInputsLevel : ProofLevel
literalScaleAdjustedThresholdBridgeInputsLevel = conditional

literalBoltzmannExponentialSuppressionInputsLevel : ProofLevel
literalBoltzmannExponentialSuppressionInputsLevel = conditional
