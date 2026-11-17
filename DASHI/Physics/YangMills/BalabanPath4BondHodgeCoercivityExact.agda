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
import DASHI.Physics.YangMills.BalabanFiniteSumRelationFibreLiftExact as SumLift
open import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact using
  (globalDirectionalEnergy; path4GlobalPoincare)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)

------------------------------------------------------------------------
-- Componentwise lift from scalar site fields to the repository's literal
-- positive-axis bond carrier.  The four bond directions are not encoded by an
-- ad-hoc tuple: they are the existing Axis4-indexed representation of BondField.
-- The componentwise <= family is lifted through the canonical finite-sum
-- relation observer; this module no longer imports directional-energy machinery
-- merely to obtain a recursive list theorem.
------------------------------------------------------------------------

RationalBondField4 : Set
RationalBondField4 = BondField side4 ℚ

bondComponent : RationalBondField4 → Axis4 → SiteField side4
bondComponent fld axis = bondFieldAsAxisIndexedSiteField fld axis

bondNormSq : RationalBondField4 → ℚ
bondNormSq fld =
  sumRational (allCyclicIndices four)
    (λ axis → globalNormSq (bondComponent fld axis))

bondReferenceDifferenceEnergy : RationalBondField4 → ℚ
bondReferenceDifferenceEnergy fld =
  sumRational (allCyclicIndices four)
    (λ axis → globalDirectionalEnergy (bondComponent fld axis))

BondComponentMeanZero : RationalBondField4 → Set
BondComponentMeanZero fld =
  ∀ axis → GlobalMeanZero4 (bondComponent fld axis)

componentwisePath4Poincare :
  ∀ fld → BondComponentMeanZero fld →
  sumRational (allCyclicIndices four)
    (λ axis → oneSixteenth * globalNormSq (bondComponent fld axis))
  ≤ bondReferenceDifferenceEnergy fld
componentwisePath4Poincare fld meanZero =
  SumLift.sumRationalMonotoneViaFibre
    (allCyclicIndices four)
    (λ axis → oneSixteenth * globalNormSq (bondComponent fld axis))
    (λ axis → globalDirectionalEnergy (bondComponent fld axis))
    (λ axis → path4GlobalPoincare
      (bondComponent fld axis) (meanZero axis))

scaledBondNormIsComponentFold : ∀ fld →
  oneSixteenth * bondNormSq fld
  ≡ sumRational (allCyclicIndices four)
      (λ axis → oneSixteenth * globalNormSq (bondComponent fld axis))
scaledBondNormIsComponentFold fld =
  sym
    (sumRationalScale
      oneSixteenth
      (allCyclicIndices four)
      (λ axis → globalNormSq (bondComponent fld axis)))

path4BondDifferencePoincare :
  ∀ fld → BondComponentMeanZero fld →
  oneSixteenth * bondNormSq fld
  ≤ bondReferenceDifferenceEnergy fld
path4BondDifferencePoincare fld meanZero =
  subst
    (λ left → left ≤ bondReferenceDifferenceEnergy fld)
    (sym (scaledBondNormIsComponentFold fld))
    (componentwisePath4Poincare fld meanZero)

------------------------------------------------------------------------
-- Gauge fixing and block penalties enter the reference Hodge form as
-- nonnegative terms.  Their literal operator identification remains separate;
-- once supplied, coercivity follows without changing the constant.
------------------------------------------------------------------------

referenceHodgeEnergy :
  RationalBondField4 → ℚ → ℚ → ℚ
referenceHodgeEnergy fld gaugeFixingEnergy blockPenaltyEnergy =
  bondReferenceDifferenceEnergy fld
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
  ∀ fld gaugeFixingEnergy blockPenaltyEnergy →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  bondReferenceDifferenceEnergy fld
  ≤ referenceHodgeEnergy fld gaugeFixingEnergy blockPenaltyEnergy
referenceDifferenceBelowHodge fld gaugeFixingEnergy blockPenaltyEnergy
  gaugeNonnegative blockNonnegative =
  baseBelowBasePlusRemainder
    (bondReferenceDifferenceEnergy fld)
    (gaugeFixingEnergy + blockPenaltyEnergy)
    (penaltySumNonnegative
      gaugeFixingEnergy blockPenaltyEnergy
      gaugeNonnegative blockNonnegative)

path4BondReferenceHodgeCoercivity :
  ∀ fld gaugeFixingEnergy blockPenaltyEnergy →
  BondComponentMeanZero fld →
  0ℚ ≤ gaugeFixingEnergy →
  0ℚ ≤ blockPenaltyEnergy →
  oneSixteenth * bondNormSq fld
  ≤ referenceHodgeEnergy fld gaugeFixingEnergy blockPenaltyEnergy
path4BondReferenceHodgeCoercivity
  fld gaugeFixingEnergy blockPenaltyEnergy
  meanZero gaugeNonnegative blockNonnegative =
  ℚP.≤-trans
    (path4BondDifferencePoincare fld meanZero)
    (referenceDifferenceBelowHodge
      fld gaugeFixingEnergy blockPenaltyEnergy
      gaugeNonnegative blockNonnegative)

path4BondComponentPoincareLevel : ProofLevel
path4BondComponentPoincareLevel = machineChecked

path4BondReferenceHodgeCoercivityLevel : ProofLevel
path4BondReferenceHodgeCoercivityLevel = machineChecked

literalGaugeBlockPenaltyIdentificationLevel : ProofLevel
literalGaugeBlockPenaltyIdentificationLevel = conditional
