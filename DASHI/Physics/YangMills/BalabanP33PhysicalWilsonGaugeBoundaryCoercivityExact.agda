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
flatDivergenceEnergy field =
  Periodic.physicalPeriodicDivergenceEnergy
    (Boundary.asPeriodicField field)

boundaryEnergy : Physical.PhysicalSU2BondField4 → ℚ
boundaryEnergy = Boundary.physicalBoundaryWrapEnergy

flatWilsonDivergenceEqualsOpenReferencePlusBoundary : ∀ field →
  flatCurlEnergy field + flatDivergenceEnergy field
  ≡ PhysicalHodge.physicalReferenceDifferenceEnergy field
    + boundaryEnergy field
flatWilsonDivergenceEqualsOpenReferencePlusBoundary field =
  trans
    (cong
      (_+ flatDivergenceEnergy field)
      (FlatWilson.flatWilsonEnergyIsPhysicalPeriodicCurl field))
    (Boundary.physicalFlatHodgeWithBoundary field)
  where
  open import Relation.Binary.PropositionalEquality using (cong)

coupledRemainderWithBoundaryExact :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  Jets.wilsonSecondVariation dataSet
    + Cancel.gaugeFirstEnergy dataSet
    - PhysicalHodge.physicalReferenceDifferenceEnergy field
  ≡ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy field)
    + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field)
    + boundaryEnergy field
coupledRemainderWithBoundaryExact field dataSet =
  let
    hodgeExact =
      flatWilsonDivergenceEqualsOpenReferencePlusBoundary field
  in
  subst
    (λ selected →
      Jets.wilsonSecondVariation dataSet
        + Cancel.gaugeFirstEnergy dataSet
        - selected
      ≡ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy field)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field)
        + boundaryEnergy field)
    (ℚRing.solve-∀
      (flatCurlEnergy field)
      (flatDivergenceEnergy field)
      (boundaryEnergy field))
    (subst
      (λ selected →
        Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - (flatCurlEnergy field + flatDivergenceEnergy field
            - boundaryEnergy field)
        ≡ selected)
      (sym hodgeExact)
      (ℚRing.solve-∀
        (Jets.wilsonSecondVariation dataSet)
        (Cancel.gaugeFirstEnergy dataSet)
        (flatCurlEnergy field)
        (flatDivergenceEnergy field)
        (boundaryEnergy field)))

boundaryAssistedSharpLower :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  - (Sharp.sharpSixteenAtomBudget * Physical.physicalSU2BondNormSq field)
    ≤ Jets.wilsonSecondVariation dataSet - flatCurlEnergy field →
  - (Budget.configuredGaugeHodgeBudget
      * Physical.physicalSU2BondNormSq field)
    ≤ Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field →
  - (Budget.sharpWilsonGaugeBudget * Physical.physicalSU2BondNormSq field)
    ≤ Jets.wilsonSecondVariation dataSet
      + Cancel.gaugeFirstEnergy dataSet
      - PhysicalHodge.physicalReferenceDifferenceEnergy field
boundaryAssistedSharpLower field dataSet wilsonLower gaugeLower =
  let
    defectsLower :
      - (Budget.sharpWilsonGaugeBudget
          * Physical.physicalSU2BondNormSq field)
      ≤ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy field)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field)
    defectsLower =
      Budget.coupledSignedLowerFromSeparateBudgets
        (Physical.physicalSU2BondNormSq field)
        (Jets.wilsonSecondVariation dataSet - flatCurlEnergy field)
        (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field)
        wilsonLower gaugeLower

    instance
      boundaryNN : NonNegative (boundaryEnergy field)
      boundaryNN = ℚ.nonNegative
        (Boundary.physicalBoundaryWrapEnergyNonnegative field)

    withBoundary :
      - (Budget.sharpWilsonGaugeBudget
          * Physical.physicalSU2BondNormSq field)
      ≤ (Jets.wilsonSecondVariation dataSet - flatCurlEnergy field)
        + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field)
        + boundaryEnergy field
    withBoundary =
      ℚP.≤-trans defectsLower
        (ℚP.p≤p+q
          ((Jets.wilsonSecondVariation dataSet - flatCurlEnergy field)
            + (Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field))
          (boundaryEnergy field))
  in
  subst
    (λ upper →
      - (Budget.sharpWilsonGaugeBudget
          * Physical.physicalSU2BondNormSq field)
      ≤ upper)
    (sym (coupledRemainderWithBoundaryExact field dataSet))
    withBoundary

literalHessianCoerciveFromPhysicalWilsonGaugeDefects :
  ∀ {Plaquette GaugeIndex ConstraintIndex}
    (field : Physical.PhysicalSU2BondField4)
    (dataSet : Jets.LiteralPhysicalSecondVariation
      Plaquette GaugeIndex ConstraintIndex) →
  PhysicalHodge.PhysicalBondComponentMeanZero field →
  Jets.ExactResidualBackground (Jets.gaugeResidual dataSet) →
  Jets.ExactResidualBackground (Jets.constraintResidual dataSet) →
  - (Sharp.sharpSixteenAtomBudget * Physical.physicalSU2BondNormSq field)
    ≤ Jets.wilsonSecondVariation dataSet - flatCurlEnergy field →
  - (Budget.configuredGaugeHodgeBudget
      * Physical.physicalSU2BondNormSq field)
    ≤ Cancel.gaugeFirstEnergy dataSet - flatDivergenceEnergy field →
  P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
    ≤ Jets.literalTotalSecondVariation dataSet
literalHessianCoerciveFromPhysicalWilsonGaugeDefects
    field dataSet meanZero gaugeExact constraintExact
    wilsonLower gaugeLower =
  let
    sharpLower =
      boundaryAssistedSharpLower
        field dataSet wilsonLower gaugeLower

    physicalLower :
      - (P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field)
      ≤ Jets.wilsonSecondVariation dataSet
        + Cancel.gaugeFirstEnergy dataSet
        - PhysicalHodge.physicalReferenceDifferenceEnergy field
    physicalLower =
      Budget.sharpCoupledLowerImpliesPhysicalSignedLower
        (Physical.physicalSU2BondNormSq field)
        (Jets.wilsonSecondVariation dataSet
          + Cancel.gaugeFirstEnergy dataSet
          - PhysicalHodge.physicalReferenceDifferenceEnergy field)
        (Budget.physicalBondNormSqNonnegative field)
        sharpLower
  in
  Cancel.literalHessianCoerciveFromWilsonGaugeHodgeDifference
    field dataSet meanZero gaugeExact constraintExact physicalLower

physicalFlatHodgeBoundaryReductionLevel : ProofLevel
physicalFlatHodgeBoundaryReductionLevel = machineChecked

physicalBoundaryAssistedRemainderLevel : ProofLevel
physicalBoundaryAssistedRemainderLevel = machineChecked

physicalWilsonGaugeDefectsToCoercivityLevel : ProofLevel
physicalWilsonGaugeDefectsToCoercivityLevel = machineChecked
