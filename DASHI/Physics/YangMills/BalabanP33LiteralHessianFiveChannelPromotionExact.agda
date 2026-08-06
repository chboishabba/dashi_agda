module DASHI.Physics.YangMills.BalabanP33LiteralHessianFiveChannelPromotionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Join the literal Wilson + gauge-fixing + block-constraint second variation
-- to the already checked five-channel coercivity theorem.  The literal
-- remainder is not supplied independently; it is defined by subtraction:
--
--   R_lit(h) = H_lit(h) - H_ref(h).
--
-- A physical identification proves that this difference is the sum of the
-- five signed cell families.  The existing exact local-to-global theorem then
-- yields
--
--   (1/32)||h||^2 <= H_lit(h).
--
-- Thus the remaining physical seam is precisely the equality of the printed
-- differentiated atoms with the five configured families and their pointwise
-- bounds.  Hessian additivity, residual subtraction and the final 1/32
-- promotion are no longer separate premises.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33FiveChannelPath4CoercivityExact as Five
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Literal

record LiteralFiveChannelHessianData
    (Background Plaquette GaugeIndex ConstraintIndex
      CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell : Set) :
    Set₁ where
  field
    fiveChannels : Five.FiveChannelPath4Data
      Background CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell

    literalJets : Background → Hodge.RationalBondField4 →
      Literal.LiteralPhysicalSecondVariation
        Plaquette GaugeIndex ConstraintIndex

    gaugeExact : ∀ background state →
      Literal.ExactResidualBackground
        (Literal.gaugeResidual (literalJets background state))

    constraintExact : ∀ background state →
      Literal.ExactResidualBackground
        (Literal.constraintResidual (literalJets background state))

    gaugeFixingEnergy blockPenaltyEnergy :
      Background → Hodge.RationalBondField4 → ℚ

    gaugeFixingEnergyNonnegative : ∀ background state →
      0ℚ ≤ gaugeFixingEnergy background state

    blockPenaltyEnergyNonnegative : ∀ background state →
      0ℚ ≤ blockPenaltyEnergy background state

    meanZero : ∀ background state → Hodge.BondComponentMeanZero state

    literalRemainderIdentification : ∀ background state →
      Literal.literalTotalSecondVariation (literalJets background state)
        - Hodge.referenceHodgeEnergy state
            (gaugeFixingEnergy background state)
            (blockPenaltyEnergy background state)
      ≡ Five.totalSignedRemainder fiveChannels background state

open LiteralFiveChannelHessianData public

literalHessianEnergy :
  ∀ {Background Plaquette GaugeIndex ConstraintIndex
      CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell} →
  LiteralFiveChannelHessianData
    Background Plaquette GaugeIndex ConstraintIndex
    CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell →
  Background → Hodge.RationalBondField4 → ℚ
literalHessianEnergy dataSet background state =
  Literal.literalTotalSecondVariation
    (literalJets dataSet background state)

literalReferencePlusRemainder :
  ∀ {Background Plaquette GaugeIndex ConstraintIndex
      CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : LiteralFiveChannelHessianData
      Background Plaquette GaugeIndex ConstraintIndex
      CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  literalHessianEnergy dataSet background state
  ≡ Hodge.referenceHodgeEnergy state
      (gaugeFixingEnergy dataSet background state)
      (blockPenaltyEnergy dataSet background state)
    + Five.totalSignedRemainder
        (fiveChannels dataSet) background state
literalReferencePlusRemainder dataSet background state =
  let
    reference = Hodge.referenceHodgeEnergy state
      (gaugeFixingEnergy dataSet background state)
      (blockPenaltyEnergy dataSet background state)
    literal = literalHessianEnergy dataSet background state
    rearrange : literal ≡ reference + (literal - reference)
    rearrange = ℚRing.solve-∀ literal reference
  in
  trans rearrange
    (cong
      (λ remainder → reference + remainder)
      (literalRemainderIdentification dataSet background state))

literalHessianCoerciveOneThirtySecond :
  ∀ {Background Plaquette GaugeIndex ConstraintIndex
      CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell}
    (dataSet : LiteralFiveChannelHessianData
      Background Plaquette GaugeIndex ConstraintIndex
      CurvatureCell TransportCell ChartCell GaugeCell ConstraintCell)
    background state →
  P33.p33PhysicalFloor * Hodge.bondNormSq state
  ≤ literalHessianEnergy dataSet background state
literalHessianCoerciveOneThirtySecond dataSet background state =
  subst
    (λ right →
      P33.p33PhysicalFloor * Hodge.bondNormSq state ≤ right)
    (sym (literalReferencePlusRemainder dataSet background state))
    (Five.fiveLocalChannelsGivePath4PhysicalCoercivity
      (fiveChannels dataSet)
      background state
      (gaugeFixingEnergy dataSet background state)
      (blockPenaltyEnergy dataSet background state)
      (meanZero dataSet background state)
      (gaugeFixingEnergyNonnegative dataSet background state)
      (blockPenaltyEnergyNonnegative dataSet background state))

literalHessianSubtractionLevel : ProofLevel
literalHessianSubtractionLevel = machineChecked

literalFiveChannelPromotionLevel : ProofLevel
literalFiveChannelPromotionLevel = machineChecked

literalPhysicalHessianOneThirtySecondLevel : ProofLevel
literalPhysicalHessianOneThirtySecondLevel = machineChecked

physicalFiveFamilyAtomIdentificationLevel : ProofLevel
physicalFiveFamilyAtomIdentificationLevel = conditional
