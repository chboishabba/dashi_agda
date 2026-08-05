module DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact where

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
-- Bind the literal physical field and the literal rational second-variation
-- data to one perturbation h.  Earlier versions additionally stored abstract
-- copies of the norm, reference, curl, divergence, Wilson and gauge energies
-- together with equality receipts.  Those copies are now unnecessary:
--
--   * the physical norm is computed from physicalFieldOf h;
--   * flat curl is computed by the rational plaquette theorem;
--   * flat divergence and the positive boundary term are computed by the
--     periodic Hodge development;
--   * Wilson and gauge values are read directly from secondVariationOf h.
--
-- The only remaining model data are therefore genuine producers from the same
-- h, plus the exact-background and componentwise mean-zero conditions.  The
-- final theorem consumes the two analytic defect estimates on those concrete
-- quantities and returns the literal 1/32 Hessian floor.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (_*_; -_; _-_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as Budget
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact as Endgame

record LiteralPhysicalPerturbationModel
    (Perturbation Plaquette GaugeIndex ConstraintIndex : Set) : Set₁ where
  field
    physicalFieldOf : Perturbation → Physical.PhysicalSU2BondField4

    secondVariationOf : Perturbation →
      Jets.LiteralPhysicalSecondVariation
        Plaquette GaugeIndex ConstraintIndex

    componentMeanZero : ∀ h →
      PhysicalHodge.PhysicalBondComponentMeanZero (physicalFieldOf h)

    gaugeExact : ∀ h →
      Jets.ExactResidualBackground
        (Jets.gaugeResidual (secondVariationOf h))

    constraintExact : ∀ h →
      Jets.ExactResidualBackground
        (Jets.constraintResidual (secondVariationOf h))

open LiteralPhysicalPerturbationModel public

literalHessianCoerciveFromSamePhysicalPerturbation :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation Plaquette GaugeIndex ConstraintIndex)
    h →
  - (Sharp.sharpSixteenAtomBudget
      * Physical.physicalSU2BondNormSq (physicalFieldOf model h))
    ≤ Jets.wilsonSecondVariation (secondVariationOf model h)
      - Endgame.flatCurlEnergy (physicalFieldOf model h) →
  - (Budget.configuredGaugeHodgeBudget
      * Physical.physicalSU2BondNormSq (physicalFieldOf model h))
    ≤ Cancel.gaugeFirstEnergy (secondVariationOf model h)
      - Endgame.flatDivergenceEnergy (physicalFieldOf model h) →
  P33.p33PhysicalFloor
    * Physical.physicalSU2BondNormSq (physicalFieldOf model h)
  ≤ Jets.literalTotalSecondVariation (secondVariationOf model h)
literalHessianCoerciveFromSamePhysicalPerturbation
    model h wilsonLower gaugeLower =
  Endgame.literalHessianCoerciveFromPhysicalWilsonGaugeDefects
    (physicalFieldOf model h)
    (secondVariationOf model h)
    (componentMeanZero model h)
    (gaugeExact model h)
    (constraintExact model h)
    wilsonLower gaugeLower

literalPhysicalPerturbationAdapterLevel : ProofLevel
literalPhysicalPerturbationAdapterLevel = machineChecked

literalSamePerturbationWilsonGaugeCoercivityLevel : ProofLevel
literalSamePerturbationWilsonGaugeCoercivityLevel = machineChecked
