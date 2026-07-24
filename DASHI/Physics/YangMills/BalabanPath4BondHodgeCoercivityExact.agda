module DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate using
  (oneSixteenth)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact using
  (globalNormSq; GlobalMeanZero4)
open import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact using
  (sumRationalMonotone)
open import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact using
  (globalDirectionalEnergy; path4GlobalPoincare)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)

------------------------------------------------------------------------
-- Componentwise lift from scalar site fields to the repository's literal
-- positive-axis bond carrier.  The four bond directions are not encoded by an
-- ad-hoc tuple: they are the existing Axis4-indexed representation of BondField.
------------------------------------------------------------------------

RationalBondField4 : Set
RationalBondField4 = BondField side4 ℚ

bondComponent : RationalBondField4 → Axis4 → SiteField side4
bondComponent field axis = bondFieldAsAxisIndexedSiteField field axis

bondNormSq : RationalBondField4 → ℚ
bondNormSq field =
  sumRational (allCyclicIndices four)
    (λ axis → globalNormSq (bondComponent field axis))

bondReferenceDifferenceEnergy : RationalBondField4 → ℚ
bondReferenceDifferenceEnergy field =
  sumRational (allCyclicIndices four)
    (λ axis → globalDirectionalEnergy (bondComponent field axis))

BondComponentMeanZero : RationalBondField4 → Set
BondComponentMeanZero field =
  ∀ axis → GlobalMeanZero4 (bondComponent field axis)

componentwisePath4Poincare :
  ∀ field → BondComponentMeanZero field →
  sumRational (allCyclicIndices four)
    (λ axis → oneSixteenth * globalNormSq (bondComponent field axis))
  ≤ bondReferenceDifferenceEnergy field
componentwisePath4Poincare field meanZero =
  sumRationalMonotone
    (allCyclicIndices four)
    (λ axis → oneSixteenth * globalNormSq (bondComponent field axis))
    (λ axis → globalDirectionalEnergy (bondComponent field axis))
    (λ axis → path4GlobalPoincare
      (bondComponent field axis) (meanZero axis))

scaledBondNormIsComponentFold : ∀ field →
  oneSixteenth * bondNormSq field
  ≡ sumRational (allCyclicIndices four)
      (λ axis → oneSixteenth * globalNormSq (bondComponent field axis))
scaledBondNormIsComponentFold field =
  sym
    (sumRationalScale
      oneSixteenth
      (allCyclicIndices four)
      (λ axis → globalNormSq (bondComponent field axis)))

path4BondDifferencePoincare :
  ∀ field → BondComponentMeanZero field →
  oneSixteenth * bondNormSq field
  ≤ bondReferenceDifferenceEnergy field
path4BondDifferencePoincare field meanZero =
  subst
    (λ left → left ≤ bondReferenceDifferenceEnergy field)
    (sym (scaledBondNormIsComponentFold field))
    (componentwisePath4Poincare field meanZero)

------------------------------------------------------------------------
-- Gauge fixing and block penalties enter the reference Hodge form as
-- nonnegative terms.  Their literal operator identification remains separate;
-- once supplied, coercivity follows without changing the constant.
------------------------------------------------------------------------

referenceHodgeEnergy :
  RationalBondField4 → ℚ → ℚ → ℚ
referenceHodgeEnergy field gaugeFixingEnergy blockPenaltyEnergy =
  bondReferenceDifferenceEnergy field
  + (gaugeFixingEnergy + blockPenaltyEnergy)

penaltySumNonnegative : ∀ gaugeFixingEnergy blockPenaltyEnergy →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  0ℚ ≤ gaugeFixingEnergy + blockPenaltyEnergy
penaltySumNonnegative gaugeFixingEnergy blockPenaltyEnergy
  gaugeNonnegative blockNonnegative =
  subst
    (λ left → left ≤ gaugeFixingEnergy + blockPenaltyEnergy)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤ gaugeNonnegative blockNonnegative)

referenceDifferenceBelowHodge :
  ∀ field gaugeFixingEnergy blockPenaltyEnergy →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  bondReferenceDifferenceEnergy field
  ≤ referenceHodgeEnergy field gaugeFixingEnergy blockPenaltyEnergy
referenceDifferenceBelowHodge field gaugeFixingEnergy blockPenaltyEnergy
  gaugeNonnegative blockNonnegative =
  baseBelowBasePlusRemainder
    (bondReferenceDifferenceEnergy field)
    (gaugeFixingEnergy + blockPenaltyEnergy)
    (penaltySumNonnegative
      gaugeFixingEnergy blockPenaltyEnergy
      gaugeNonnegative blockNonnegative)

path4BondReferenceHodgeCoercivity :
  ∀ field gaugeFixingEnergy blockPenaltyEnergy →
  BondComponentMeanZero field →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  oneSixteenth * bondNormSq field
  ≤ referenceHodgeEnergy field gaugeFixingEnergy blockPenaltyEnergy
path4BondReferenceHodgeCoercivity
  field gaugeFixingEnergy blockPenaltyEnergy
  meanZero gaugeNonnegative blockNonnegative =
  ℚP.≤-trans
    (path4BondDifferencePoincare field meanZero)
    (referenceDifferenceBelowHodge
      field gaugeFixingEnergy blockPenaltyEnergy
      gaugeNonnegative blockNonnegative)

path4BondComponentPoincareLevel : ProofLevel
path4BondComponentPoincareLevel = machineChecked

path4BondReferenceHodgeCoercivityLevel : ProofLevel
path4BondReferenceHodgeCoercivityLevel = machineChecked

literalGaugeBlockPenaltyIdentificationLevel : ProofLevel
literalGaugeBlockPenaltyIdentificationLevel = conditional
