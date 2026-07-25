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
bondComponent bondF axis = bondFieldAsAxisIndexedSiteField bondF axis

bondNormSq : RationalBondField4 → ℚ
bondNormSq bondF =
  sumRational (allCyclicIndices four)
    (λ axis → globalNormSq (bondComponent bondF axis))

bondReferenceDifferenceEnergy : RationalBondField4 → ℚ
bondReferenceDifferenceEnergy bondF =
  sumRational (allCyclicIndices four)
    (λ axis → globalDirectionalEnergy (bondComponent bondF axis))

BondComponentMeanZero : RationalBondField4 → Set
BondComponentMeanZero bondF =
  ∀ axis → GlobalMeanZero4 (bondComponent bondF axis)

componentwisePath4Poincare :
  ∀ bondF → BondComponentMeanZero bondF →
  sumRational (allCyclicIndices four)
    (λ axis → oneSixteenth * globalNormSq (bondComponent bondF axis))
  ≤ bondReferenceDifferenceEnergy bondF
componentwisePath4Poincare bondF meanZero =
  sumRationalMonotone
    (allCyclicIndices four)
    (λ axis → oneSixteenth * globalNormSq (bondComponent bondF axis))
    (λ axis → globalDirectionalEnergy (bondComponent bondF axis))
    (λ axis → path4GlobalPoincare
      (bondComponent bondF axis) (meanZero axis))

scaledBondNormIsComponentFold : ∀ bondF →
  oneSixteenth * bondNormSq bondF
  ≡ sumRational (allCyclicIndices four)
      (λ axis → oneSixteenth * globalNormSq (bondComponent bondF axis))
scaledBondNormIsComponentFold bondF =
  sym
    (sumRationalScale
      oneSixteenth
      (allCyclicIndices four)
      (λ axis → globalNormSq (bondComponent bondF axis)))

path4BondDifferencePoincare :
  ∀ bondF → BondComponentMeanZero bondF →
  oneSixteenth * bondNormSq bondF
  ≤ bondReferenceDifferenceEnergy bondF
path4BondDifferencePoincare bondF meanZero =
  subst
    (λ left → left ≤ bondReferenceDifferenceEnergy bondF)
    (sym (scaledBondNormIsComponentFold bondF))
    (componentwisePath4Poincare bondF meanZero)

------------------------------------------------------------------------
-- Gauge fixing and block penalties enter the reference Hodge form as
-- nonnegative terms.  Their literal operator identification remains separate;
-- once supplied, coercivity follows without changing the constant.
------------------------------------------------------------------------

referenceHodgeEnergy :
  RationalBondField4 → ℚ → ℚ → ℚ
referenceHodgeEnergy bondF gaugeFixingEnergy blockPenaltyEnergy =
  bondReferenceDifferenceEnergy bondF
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
  ∀ bondF gaugeFixingEnergy blockPenaltyEnergy →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  bondReferenceDifferenceEnergy bondF
  ≤ referenceHodgeEnergy bondF gaugeFixingEnergy blockPenaltyEnergy
referenceDifferenceBelowHodge bondF gaugeFixingEnergy blockPenaltyEnergy
  gaugeNonnegative blockNonnegative =
  baseBelowBasePlusRemainder
    (bondReferenceDifferenceEnergy bondF)
    (gaugeFixingEnergy + blockPenaltyEnergy)
    (penaltySumNonnegative
      gaugeFixingEnergy blockPenaltyEnergy
      gaugeNonnegative blockNonnegative)

path4BondReferenceHodgeCoercivity :
  ∀ bondF gaugeFixingEnergy blockPenaltyEnergy →
  BondComponentMeanZero bondF →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  oneSixteenth * bondNormSq bondF
  ≤ referenceHodgeEnergy bondF gaugeFixingEnergy blockPenaltyEnergy
path4BondReferenceHodgeCoercivity
  bondF gaugeFixingEnergy blockPenaltyEnergy
  meanZero gaugeNonnegative blockNonnegative =
  ℚP.≤-trans
    (path4BondDifferencePoincare bondF meanZero)
    (referenceDifferenceBelowHodge
      bondF gaugeFixingEnergy blockPenaltyEnergy
      gaugeNonnegative blockNonnegative)

path4BondComponentPoincareLevel : ProofLevel
path4BondComponentPoincareLevel = machineChecked

path4BondReferenceHodgeCoercivityLevel : ProofLevel
path4BondReferenceHodgeCoercivityLevel = machineChecked

literalGaugeBlockPenaltyIdentificationLevel : ProofLevel
literalGaugeBlockPenaltyIdentificationLevel = conditional
