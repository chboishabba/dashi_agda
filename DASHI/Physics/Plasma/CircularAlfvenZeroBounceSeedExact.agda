module DASHI.Physics.Plasma.CircularAlfvenZeroBounceSeedExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ElsasserCounterpropagatingInteractionBidiExact as Counter
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as AField
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- CIRCULARLY-POLARIZED ALFVEN ZERO-BOUNCE SEED
--
-- Local slab seed:
--   B = B0 zhat + a (cos phi xhat + sin phi yhat)
--   phi = k z - omega t
--   u = - b_perp / sqrt(mu0 rho)
--   omega = k v_A.
--
-- Then |B|^2 = B0^2 + a^2 is constant, so the adiabatic mirror term
-- -mu grad_parallel |B| vanishes.  The same seed is a pure one-direction
-- Elsasser state in homogeneous ideal MHD, hence it sits on the repo's exact
-- nonlinear-depletion boundary.  Toroidal curvature remains open separately.
------------------------------------------------------------------------

record CircularAlfvenZeroBounceSeed
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor circular-alfven-zero-bounce-seed
  field
    guideFieldReceipt : Set
    circularTransverseFieldReceipt : Set
    phaseLawReceipt : Set
    alfvenDispersionReceipt : Set
    velocityMagneticAlfvenRelationReceipt : Set

    divergenceFreeFieldReceipt : Set
    constantMagneticMagnitudeReceipt : Set
    zeroParallelMagneticMagnitudeGradientReceipt : Set
    zeroMagneticMirrorForceReceipt : Set
    zeroBounce : ZeroBounce.ZeroBounceReceipt population

    idealInductionEquationReceipt : Set
    idealMomentumEquationReceipt : Set
    incompressibilityReceipt : Set
    pureElsasserState : Counter.PureElsasserState
    pureElsasserNonlinearDepletion :
      Counter.PureStateNonlinearDepletion pureElsasserState

    magneticVectorPotentialCarrierReused : Set
    sourceReference : String
    localModelReference : String

open CircularAlfvenZeroBounceSeed public

record CircularAlfvenSeedBoundary : Set where
  constructor circular-alfven-seed-boundary
  field
    constantMagnitudeEliminatesAdiabaticMirrorForce : Bool
    constantMagnitudeEliminatesAdiabaticMirrorForceIsTrue :
      constantMagnitudeEliminatesAdiabaticMirrorForce ≡ true

    zeroMirrorForceImpliesZeroCurvatureDrift : Bool
    zeroMirrorForceImpliesZeroCurvatureDriftIsFalse :
      zeroMirrorForceImpliesZeroCurvatureDrift ≡ false

    localSlabSolutionAlreadyProvesToroidalReactor : Bool
    localSlabSolutionAlreadyProvesToroidalReactorIsFalse :
      localSlabSolutionAlreadyProvesToroidalReactor ≡ false

    pureElsasserBoundaryReused : Bool
    pureElsasserBoundaryReusedIsTrue :
      pureElsasserBoundaryReused ≡ true

canonicalCircularAlfvenSeedBoundary : CircularAlfvenSeedBoundary
canonicalCircularAlfvenSeedBoundary =
  circular-alfven-seed-boundary
    true refl
    false refl
    false refl
    true refl

classicalCircularAlfvenSource : String
classicalCircularAlfvenSource =
  "Large-amplitude circularly polarized Alfven waves are exact nonlinear ideal-MHD solutions with constant |B|; see Goldstein et al., ApJ 219 (1978) and modern exact nonlinear constant-|B| Alfven-wave literature."
