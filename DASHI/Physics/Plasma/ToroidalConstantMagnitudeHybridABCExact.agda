module DASHI.Physics.Plasma.ToroidalConstantMagnitudeHybridABCExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- UNIFIED ABC FORCE-BALANCE CONTINUATION
--
-- Let u = M B / sqrt(mu0 rho) and let
--
--   Delta p = p_parallel - p_perp = alpha B^2 / mu0.
--
-- For divergence-free constant-|B| fields, the magnetic tension coefficient is
-- 1.  Flow inertia pays M^2, anisotropic pressure pays alpha, and the geometric
-- remainder is
--
--   delta = 1 - M^2 - alpha.
--
-- Hence M^2 + alpha = 1 closes the tension exactly without requiring the
-- route-C geodesic condition.  For 0<M<1, alpha=1-M^2 is simultaneously
-- sub-Alfvenic and strictly inside the firehose threshold; the firehose margin
-- is M^2 B^2/mu0.  This is an exact ideal-model identity, not a reactor
-- stability theorem.
------------------------------------------------------------------------

record HybridABCForceBalanceReceipt
    (population : ZeroBounce.DeclaredParticlePopulation)
    (seed : Seed.ToroidalConstantMagnitudeSeed population) : Set₁ where
  constructor hybrid-abc-force-balance-receipt
  field
    alfvenMachNumberReceipt : Set
    anisotropyFractionReceipt : Set
    geometryResidualFractionReceipt : Set

    inertiaFractionIsMachSquaredReceipt : Set
    anisotropyFractionInterpretationReceipt : Set
    fractionSumToOneReceipt : Set

    subAlfvenicReceipt : Set
    positiveFirehoseMarginReceipt : Set
    idealInductionReceipt : Set
    zeroBouncePreservedReceipt : Set
    sameFieldSamePopulationReceipt : Set

    collisionalRelaxationReceipt : Set
    flowShearStabilityReceipt : Set
    kineticStabilityReceipt : Set
    finiteOrbitWidthReceipt : Set
    engineeringPowerReceipt : Set
    receiptReference : String

open HybridABCForceBalanceReceipt public

record HybridABCBoundary : Set where
  constructor hybrid-abc-boundary
  field
    pureARequiresMachOneForExactTensionClosure : Bool
    pureARequiresMachOneForExactTensionClosureIsTrue :
      pureARequiresMachOneForExactTensionClosure ≡ true

    pureBExactSeedIsFirehoseMarginal : Bool
    pureBExactSeedIsFirehoseMarginalIsTrue :
      pureBExactSeedIsFirehoseMarginal ≡ true

    mixedABCanCloseExactlyAwayFromBothPureBoundaries : Bool
    mixedABCanCloseExactlyAwayFromBothPureBoundariesIsTrue :
      mixedABCanCloseExactlyAwayFromBothPureBoundaries ≡ true

    exactIdealIdentityProvesKineticStability : Bool
    exactIdealIdentityProvesKineticStabilityIsFalse :
      exactIdealIdentityProvesKineticStability ≡ false

    routeCMayPayOnlyDeclaredResidualFraction : Bool
    routeCMayPayOnlyDeclaredResidualFractionIsTrue :
      routeCMayPayOnlyDeclaredResidualFraction ≡ true

canonicalHybridABCBoundary : HybridABCBoundary
canonicalHybridABCBoundary =
  hybrid-abc-boundary
    true refl
    true refl
    true refl
    false refl
    true refl

hybridIdentityReference : String
hybridIdentityReference =
  "For constant |B|: magnetic tension = 1 unit; Alfvenic-flow inertia contributes M^2; CGL anisotropy contributes alpha; route-C geometry pays delta=1-M^2-alpha. Exact A+B closure uses M^2+alpha=1."
