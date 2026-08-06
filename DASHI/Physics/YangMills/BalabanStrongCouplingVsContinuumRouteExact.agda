module DASHI.Physics.YangMills.BalabanStrongCouplingVsContinuumRouteExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", official Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Type-separate the published fixed-lattice strong-coupling theorem from the
-- weak-coupling/cutoff-removal route required for a four-dimensional continuum
-- Yang--Mills theory.  The stochastic route can independently discharge a
-- genuine Stage-II theorem in its regime: unique infinite-volume lattice
-- measure, functional inequalities and exponential covariance decay.  It does
-- not identify measures across changing lattice spacings or prove the
-- asymptotically-free continuum limit.
--
-- Exact arithmetic shows the four-dimensional SU Bakry--Emery margin is already
-- negative at inverse-coupling magnitude one:
--
--   1/2 - 24 = -47/2.
--
-- Thus the published sufficient condition cannot simply be iterated into an
-- inverse-coupling regime of order one or larger.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Rational.Base using (ℚ; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanStrongCouplingSUFourDimensionalMarginExact as Strong

data YangMillsGapRoute : Set where
  selectedBackgroundRGRoute : YangMillsGapRoute
  stochasticFunctionalInequalityRoute : YangMillsGapRoute

data ConstructionStage : Set where
  finiteVolumeHessianStage : ConstructionStage
  infiniteVolumeFixedLatticeStage : ConstructionStage
  cutoffRemovalContinuumStage : ConstructionStage
  reconstructedHamiltonianStage : ConstructionStage

record RouteCapabilities : Set where
  constructor routeCapabilities
  field
    finiteSelectedBackgroundPropagator : Bool
    uniqueInfiniteVolumeLatticeMeasure : Bool
    logSobolevAndPoincare : Bool
    exponentialLatticeCovarianceDecay : Bool
    changingLatticeSpacingControl : Bool
    asymptoticallyFreeContinuumLimit : Bool
    osterwalderSchraderReconstruction : Bool

open RouteCapabilities public

capabilities : YangMillsGapRoute → RouteCapabilities
capabilities selectedBackgroundRGRoute =
  routeCapabilities true false false false true true true
capabilities stochasticFunctionalInequalityRoute =
  routeCapabilities false true true true false false false

routesAreDistinct :
  selectedBackgroundRGRoute ≡ stochasticFunctionalInequalityRoute → ⊥
routesAreDistinct ()

stochasticRouteHasFixedLatticeGapCapability :
  exponentialLatticeCovarianceDecay
    (capabilities stochasticFunctionalInequalityRoute)
  ≡ true
stochasticRouteHasFixedLatticeGapCapability = refl

stochasticRouteDoesNotSupplyCutoffRemoval :
  changingLatticeSpacingControl
    (capabilities stochasticFunctionalInequalityRoute)
  ≡ false
stochasticRouteDoesNotSupplyCutoffRemoval = refl

rgRouteDoesNotYetInheritPublishedStochasticGap :
  uniqueInfiniteVolumeLatticeMeasure
    (capabilities selectedBackgroundRGRoute)
  ≡ false
rgRouteDoesNotYetInheritPublishedStochasticGap = refl

unitInverseCoupling : ℚ
unitInverseCoupling = + 1 / 1

unitInverseCouplingMarginExact :
  Strong.suNormalizedBakryEmeryMargin unitInverseCoupling
  ≡ -[1+ 46 ] / 2
unitInverseCouplingMarginExact = solve []

record StochasticRouteImportBridge : Set₁ where
  field
    repositoryActionConventionMatches : Set
    repositoryBetaMatchesPublishedBeta : Set
    repositoryFiniteVolumeMeasureMatches : Set
    repositoryObservableClassEmbedsInCylinderFunctions : Set
    publishedCommutatorBoundsTransport : Set
    publishedInfiniteVolumeMeasureImported : Set

-- No bridge is inhabited merely from rho=1/8192 or from the selected Hessian
-- floor.  The two routes are complementary unless these representation seams
-- are proved explicitly.
