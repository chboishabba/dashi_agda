module DASHI.Physics.Plasma.ToroidalConstantMagnitudeCGLAnisotropyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalConstantMagnitudeZeroBounceSeedExact as Seed
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- ROUTE B: CGL / PRESSURE-ANISOTROPIC FORCE BALANCE
--
-- For div B = 0 and constant |B|, div b = 0 and
--
--   J x B = (B^2/mu0) kappa.
--
-- For P = p_perp I + (p_parallel-p_perp) b b with constant p_perp,p_parallel,
--
--   div P = (p_parallel-p_perp) kappa.
--
-- Hence Delta p = p_parallel-p_perp = B^2/mu0 closes the force balance.
-- This exact seed is firehose-marginal, so it is a mathematical boundary, not
-- an accepted operating point.
------------------------------------------------------------------------

record CGLAnisotropicBalanceReceipt
    (population : ZeroBounce.DeclaredParticlePopulation)
    (seed : Seed.ToroidalConstantMagnitudeSeed population) : Set₁ where
  constructor cgl-anisotropic-balance-receipt
  field
    gyrotropicPressureTensorReceipt : Set
    constantParallelPressureReceipt : Set
    constantPerpendicularPressureReceipt : Set
    pressureAnisotropyEqualsMagneticPressureReceipt : Set
    pressureTensorDivergenceEqualsMagneticTensionReceipt : Set
    zeroBouncePreservedReceipt : Set
    sameFieldSamePopulationReceipt : Set
    kineticClosureValidityReceipt : Set
    firehoseDistanceReceipt : Set
    mirrorAndOtherAnisotropyStabilityReceipt : Set
    receiptReference : String

open CGLAnisotropicBalanceReceipt public

record CGLAnisotropyBoundary : Set where
  constructor cgl-anisotropy-boundary
  field
    exactConstantPressureSeedExists : Bool
    exactConstantPressureSeedExistsIsTrue :
      exactConstantPressureSeedExists ≡ true

    exactSeedIsStrictlyInsideFirehoseStableRegion : Bool
    exactSeedIsStrictlyInsideFirehoseStableRegionIsFalse :
      exactSeedIsStrictlyInsideFirehoseStableRegion ≡ false

    exactCGLClosureProvesKineticStability : Bool
    exactCGLClosureProvesKineticStabilityIsFalse :
      exactCGLClosureProvesKineticStability ≡ false

    saferAnisotropicContinuationRequiresAdditionalGradientOrFlow : Bool
    saferAnisotropicContinuationRequiresAdditionalGradientOrFlowIsTrue :
      saferAnisotropicContinuationRequiresAdditionalGradientOrFlow ≡ true

canonicalCGLAnisotropyBoundary : CGLAnisotropyBoundary
canonicalCGLAnisotropyBoundary =
  cgl-anisotropy-boundary
    true refl
    false refl
    false refl
    true refl

cglIdentityReference : String
cglIdentityReference =
  "For constant |B| and div B=0: JxB=(B^2/mu0)kappa. For constant gyrotropic pressures, div P=(p_parallel-p_perp)kappa. Exact closure uses Delta p=B^2/mu0 and is firehose-marginal."
