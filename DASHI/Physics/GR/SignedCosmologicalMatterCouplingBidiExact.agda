module DASHI.Physics.GR.SignedCosmologicalMatterCouplingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Laws.GravityCosmologyLaws as Laws
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact as Source

------------------------------------------------------------------------
-- SIGNED COSMOLOGICAL MATTER COUPLING
--
-- At the schematic Friedmann matter-term level, positive numerical factors
-- leave sign(G rho) as the relevant sign coordinate.  This owner tracks that
-- sign only.  Curvature, Lambda, pressure, continuity, initial data, stability,
-- and the existence of a self-consistent cosmological solution remain separate.
------------------------------------------------------------------------

data CosmologicalMatterTermOrientation : Set where
  positiveMatterContribution : CosmologicalMatterTermOrientation
  zeroMatterContribution : CosmologicalMatterTermOrientation
  negativeMatterContribution : CosmologicalMatterTermOrientation

matterTermOrientation :
  Signed.CouplingSign → Source.SourceSign → CosmologicalMatterTermOrientation
matterTermOrientation Signed.zeroCoupling density = zeroMatterContribution
matterTermOrientation coupling Source.zeroSource = zeroMatterContribution
matterTermOrientation Signed.positiveCoupling Source.positiveSource = positiveMatterContribution
matterTermOrientation Signed.positiveCoupling Source.negativeSource = negativeMatterContribution
matterTermOrientation Signed.negativeCoupling Source.positiveSource = negativeMatterContribution
matterTermOrientation Signed.negativeCoupling Source.negativeSource = positiveMatterContribution

------------------------------------------------------------------------
-- Coarse sign collision.
------------------------------------------------------------------------

data CosmologySignFixture : Set where
  negativeGPositiveDensity : CosmologySignFixture
  positiveGNegativeEffectiveDensity : CosmologySignFixture

fixtureCoupling : CosmologySignFixture → Signed.CouplingSign
fixtureCoupling negativeGPositiveDensity = Signed.negativeCoupling
fixtureCoupling positiveGNegativeEffectiveDensity = Signed.positiveCoupling

fixtureDensity : CosmologySignFixture → Source.SourceSign
fixtureDensity negativeGPositiveDensity = Source.positiveSource
fixtureDensity positiveGNegativeEffectiveDensity = Source.negativeSource

coarseMatterTermObserver : CosmologySignFixture → CosmologicalMatterTermOrientation
coarseMatterTermObserver fixture =
  matterTermOrientation (fixtureCoupling fixture) (fixtureDensity fixture)

cosmologicalMatterTermCollision :
  coarseMatterTermObserver negativeGPositiveDensity
    ≡ coarseMatterTermObserver positiveGNegativeEffectiveDensity
cosmologicalMatterTermCollision = refl

record RefinedCosmologySignObserver : Set where
  constructor refined-cosmology-sign-observer
  field
    couplingSign : Signed.CouplingSign
    densitySign : Source.SourceSign

refinedCosmologyObserve : CosmologySignFixture → RefinedCosmologySignObserver
refinedCosmologyObserve fixture =
  refined-cosmology-sign-observer (fixtureCoupling fixture) (fixtureDensity fixture)

refinedCosmologyFixturesDistinct :
  refinedCosmologyObserve negativeGPositiveDensity
    ≡ refinedCosmologyObserve positiveGNegativeEffectiveDensity → ⊥
refinedCosmologyFixturesDistinct ()

------------------------------------------------------------------------
-- Reuse marker for the existing cosmological dynamics carrier.
------------------------------------------------------------------------

record SignedCosmologyProbe (cosmology : Laws.CosmologicalDynamics) : Set₁ where
  constructor signed-cosmology-probe
  field
    couplingSign : Signed.CouplingSign
    densitySign : Source.SourceSign
    matterOrientation : CosmologicalMatterTermOrientation
    matterOrientationMatches :
      matterOrientation ≡ matterTermOrientation couplingSign densitySign
    usesExistingScaleFactor : Laws.CosmologicalDynamics.ScaleFactor cosmology → Set
    usesExistingEnergyDensity : Laws.CosmologicalDynamics.EnergyDensity cosmology → Set
    usesExistingPressure : Laws.CosmologicalDynamics.Pressure cosmology → Set
    usesExistingCurvature : Laws.CosmologicalDynamics.Curvature cosmology → Set
    usesExistingCosmologicalConstant :
      Laws.CosmologicalDynamics.CosmologicalConstant cosmology → Set
    SignedCosmologyAdequacy : Set
    signedCosmologyAdequacy : SignedCosmologyAdequacy

open SignedCosmologyProbe public

record SignedCosmologyBoundary : Set where
  constructor signed-cosmology-boundary
  field
    friedmannMatterTermSignAloneDeterminesWhetherGOrDensityWasNegative : Bool
    negativeGAutomaticallyEqualsNegativeEnergyDensity : Bool
    negativeGAutomaticallyEqualsPositiveCosmologicalConstant : Bool
    negativeGAutomaticallyExplainsAcceleratedExpansion : Bool
    continuityEquationMustRemainSeparatelySatisfied : Bool
    curvatureAndLambdaRemainIndependentCoordinates : Bool
    selfConsistentNegativeGCosmologyRequiresReSolvedDynamics : Bool
    cosmologicalObservationMayConstrainButNotUniquelyIdentifyGSign : Bool

canonicalSignedCosmologyBoundary : SignedCosmologyBoundary
canonicalSignedCosmologyBoundary =
  signed-cosmology-boundary false false false false true true true true
