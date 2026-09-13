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
-- Same-object reuse: consume literal objects from the existing cosmological
-- dynamics carrier.  The sign fibre is extra structure, not a replacement for
-- the actual scale-factor, density, pressure, curvature or equation objects.
------------------------------------------------------------------------

record SignedCosmologyProbe (cosmology : Laws.CosmologicalDynamics) : Set₁ where
  constructor signed-cosmology-probe
  field
    couplingSign : Signed.CouplingSign
    densitySign : Source.SourceSign
    matterOrientation : CosmologicalMatterTermOrientation
    matterOrientationMatches :
      matterOrientation ≡ matterTermOrientation couplingSign densitySign

    cosmicTime : Laws.CosmologicalDynamics.CosmicTime cosmology
    scaleFactorAtTime : Laws.CosmologicalDynamics.ScaleFactor cosmology
    scaleFactorMatches :
      Laws.CosmologicalDynamics.scaleFactor cosmology cosmicTime
        ≡ scaleFactorAtTime

    energyDensityAtTime : Laws.CosmologicalDynamics.EnergyDensity cosmology
    energyDensityMatches :
      Laws.CosmologicalDynamics.density cosmology cosmicTime
        ≡ energyDensityAtTime

    pressureAtTime : Laws.CosmologicalDynamics.Pressure cosmology
    pressureMatches :
      Laws.CosmologicalDynamics.pressure cosmology cosmicTime
        ≡ pressureAtTime

    curvature : Laws.CosmologicalDynamics.Curvature cosmology
    cosmologicalConstant :
      Laws.CosmologicalDynamics.CosmologicalConstant cosmology

    friedmannEquation : Laws.CosmologicalDynamics.Equation cosmology
    friedmannEquationMatches :
      Laws.CosmologicalDynamics.friedmannEquation
        cosmology curvature cosmologicalConstant
        ≡ friedmannEquation

    accelerationEquation : Laws.CosmologicalDynamics.Equation cosmology
    accelerationEquationMatches :
      Laws.CosmologicalDynamics.accelerationEquation
        cosmology cosmologicalConstant
        ≡ accelerationEquation

    continuityEquation : Laws.CosmologicalDynamics.Equation cosmology
    continuityEquationMatches :
      Laws.CosmologicalDynamics.continuityEquation cosmology
        ≡ continuityEquation

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
    exactExistingCosmologicalDynamicsObjectsRequired : Bool

canonicalSignedCosmologyBoundary : SignedCosmologyBoundary
canonicalSignedCosmologyBoundary =
  signed-cosmology-boundary false false false false true true true true true
