module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Assemble the corrected physical coercivity reduction without an abstract
-- flat-Hodge compatibility field.  For the actual PhysicalSU2BondField4 h:
--
--   * the rational four-link calculation constructs H_curl^flat(h);
--   * the periodic finite-difference theorem constructs H_div^flat(h);
--   * the open/periodic bridge constructs a nonnegative boundary energy B(h);
--   * exact finite algebra proves
--
--       H_curl^flat(h) + H_div^flat(h)
--         = H_diff^open(h) + B(h).
--
-- Hence
--
--   H_W(A;h)+H_gf(A;h)-H_diff^open(h)
--     = [H_W-H_curl^flat]
--       + [H_gf-H_div^flat]
--       + B(h).
--
-- The boundary term is positive and assists the lower bound.  Therefore the
-- two genuine analytic producers
--
--   -(13/196608)||h||^2 <= H_W-H_curl^flat,
--   -(1536/196608)||h||^2 <= H_gf-H_div^flat
--
-- imply the literal 1/32 Hessian floor, with exact remaining slack
-- 4595/196608.  The formerly assumed Wilson-minus-open-gradient comparison is
-- completely removed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as Budget
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as FlatWilson
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Boundary

flatCurlEnergy : Physical.PhysicalSU2BondField4 → ℚ
flatCurlEnergy = FlatWilson.flatWilsonEnergy

flatDivergenceEnergy : Physical.PhysicalSU2BondField4 → ℚ
flatDivergenceEnergy fieldValue =
  Periodic.physicalPeriodicDivergenceEnergy
    (Boundary.asPeriodicField fieldValue)

boundaryEnergy : Physical.PhysicalSU2BondField4 → ℚ
boundaryEnergy = Boundary.physicalBoundaryWrapEnergy

flatWilsonDivergenceEqualsOpenReferencePlusBoundary : ∀ fieldValue →
  flatCurlEnergy fieldValue + flatDivergenceEnergy fieldValue
  ≡ PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
    + boundaryEnergy fieldValue
flatWilsonDivergenceEqualsOpenReferencePlusBoundary fieldValue =
  trans
    (cong
      (_+ flatDivergenceEnergy fieldValue)
      (FlatWilson.flatWilsonEnergyIsPhysicalPeriodicCurl fieldValue))
    (Boundary.physicalFlatHodgeWithBoundary fieldValue)
  where
  open import Relation.Binary.PropositionalEquality using (cong)

coupledRemainderWithBoundaryExact :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (fieldValue : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  Jets.wilsonSecondVariation dataSet
    + Cancel.gaugeFirstEnergy dataSet
    - PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
  ≡ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue)
    + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue)
    + boundaryEnergy fieldValue
coupledRemainderWithBoundaryExact fieldValue dataSet =
  let
    hodgeExact =
      flatWilsonDivergenceEqualsOpenReferencePlusBoundary fieldValue
  in
  subst
    (λ selected →
      Jets.wilsonSecondVariation dataSet
        + Cancel.gaugeFirstEnergy dataSet
        - selected
      ≡ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue)
        + boundaryEnergy fieldValue)
    (ℚRing.solve-∀
      (flatCurlEnergy fieldValue)
      (flatDivergenceEnergy fieldValue)
      (boundaryEnergy fieldValue))
    (subst
      (λ selected →
        Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - (flatCurlEnergy fieldValue + flatDivergenceEnergy fieldValue
            - boundaryEnergy fieldValue)
        ≡ selected)
      (sym hodgeExact)
      (ℚRing.solve-∀
        (Jets.wilsonSecondVariation dataSet)
        (Cancel.gaugeFirstEnergy dataSet)
        (flatCurlEnergy fieldValue)
        (flatDivergenceEnergy fieldValue)
        (boundaryEnergy fieldValue)))

boundaryAssistedSharpLower :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (fieldValue : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  - (Sharp.sharpSixteenAtomBudget * Physical.physicalSU2BondNormSq fieldValue)
    ≤ Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue →
  - (Budget.configuredGaugeHodgeBudget
      * Physical.physicalSU2BondNormSq fieldValue)
    ≤ Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue →
  - (Budget.sharpWilsonGaugeBudget * Physical.physicalSU2BondNormSq fieldValue)
    ≤ Jets.wilsonSecondVariation dataSet
      + Cancel.gaugeFirstEnergy dataSet
      - PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
boundaryAssistedSharpLower fieldValue dataSet wilsonLower gaugeLower =
  let
    defectsLower :
      - (Budget.sharpWilsonGaugeBudget
          * Physical.physicalSU2BondNormSq fieldValue)
      ≤ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue)
    defectsLower =
      Budget.coupledSignedLowerFromSeparateBudgets
        (Physical.physicalSU2BondNormSq fieldValue)
        (Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue)
        (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue)
        wilsonLower gaugeLower

    instance
      boundaryNN : NonNegative (boundaryEnergy fieldValue)
      boundaryNN = ℚ.nonNegative
        (Boundary.physicalBoundaryWrapEnergyNonnegative fieldValue)

    withBoundary :
      - (Budget.sharpWilsonGaugeBudget
          * Physical.physicalSU2BondNormSq fieldValue)
      ≤ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue)
        + boundaryEnergy fieldValue
    withBoundary =
      ℚP.≤-trans defectsLower
        (ℚP.p≤p+q
          ((Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue)
            + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue))
          (boundaryEnergy fieldValue))
  in
  subst
    (λ upper →
      - (Budget.sharpWilsonGaugeBudget
          * Physical.physicalSU2BondNormSq fieldValue)
      ≤ upper)
    (sym (coupledRemainderWithBoundaryExact fieldValue dataSet))
    withBoundary

literalHessianCoerciveFromPhysicalWilsonGaugeDefects :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (fieldValue : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  PhysicalHodge.PhysicalBondComponentMeanZero fieldValue →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  - (Sharp.sharpSixteenAtomBudget * Physical.physicalSU2BondNormSq fieldValue)
    ≤ Jets.wilsonSecondVariation dataSet - flatCurlEnergy fieldValue →
  - (Budget.configuredGaugeHodgeBudget
      * Physical.physicalSU2BondNormSq fieldValue)
    ≤ Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy fieldValue →
  P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq fieldValue
    ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveFromPhysicalWilsonGaugeDefects
    fieldValue dataSet meanZero gaugeExact constraintExact
    wilsonLower gaugeLower =
  let
    sharpLower =
      boundaryAssistedSharpLower
        fieldValue dataSet wilsonLower gaugeLower

    physicalLower :
      - (P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq fieldValue)
      ≤ Jets.wilsonSecondVariation dataSet
        + Cancel.gaugeFirstEnergy dataSet
        - PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
    physicalLower =
      Budget.sharpCoupledLowerImpliesPhysicalSignedLower
        (Physical.physicalSU2BondNormSq fieldValue)
        (Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue)
        (Budget.physicalBondNormSqNonnegative fieldValue)
        sharpLower
  in
  Cancel.literalHessianCoerciveFromWilsonGaugeHodgeDifference
    fieldValue dataSet meanZero gaugeExact constraintExact physicalLower

physicalFlatHodgeBoundaryReductionLevel : ProofLevel
physicalFlatHodgeBoundaryReductionLevel = machineChecked

physicalBoundaryAssistedRemainderLevel : ProofLevel
physicalBoundaryAssistedRemainderLevel = machineChecked

physicalWilsonGaugeDefectsToCoercivityLevel : ProofLevel
physicalWilsonGaugeDefectsToCoercivityLevel = machineChecked
