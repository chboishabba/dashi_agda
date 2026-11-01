module DASHI.Physics.GR.SignedNewtonianLimitBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Laws.GravityCosmologyLaws as Laws
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact as Source

------------------------------------------------------------------------
-- SIGNED NEWTONIAN / POISSON LIMIT
--
-- In the ordinary weak-field schematic relation
--
--   nabla^2 Phi = 4 pi G rho,
--
-- positive 4 pi means the source-side sign is sign(G) * sign(rho).  This
-- owner tracks only that sign fibre.  It does not claim that a complete
-- negative-G Newtonian limit has been derived from the repo's GR carrier.
------------------------------------------------------------------------

data PoissonSourceOrientation : Set where
  positivePoissonSource : PoissonSourceOrientation
  zeroPoissonSource : PoissonSourceOrientation
  negativePoissonSource : PoissonSourceOrientation

poissonSourceOrientation :
  Signed.CouplingSign → Source.SourceSign → PoissonSourceOrientation
poissonSourceOrientation Signed.zeroCoupling density = zeroPoissonSource
poissonSourceOrientation coupling Source.zeroSource = zeroPoissonSource
poissonSourceOrientation Signed.positiveCoupling Source.positiveSource = positivePoissonSource
poissonSourceOrientation Signed.positiveCoupling Source.negativeSource = negativePoissonSource
poissonSourceOrientation Signed.negativeCoupling Source.positiveSource = negativePoissonSource
poissonSourceOrientation Signed.negativeCoupling Source.negativeSource = positivePoissonSource

data RadialResponseOrientation : Set where
  attractiveTowardPositiveSource : RadialResponseOrientation
  noNewtonianSourceResponse : RadialResponseOrientation
  repulsiveAwayFromPositiveSource : RadialResponseOrientation

positiveDensityRadialResponse : Signed.CouplingSign → RadialResponseOrientation
positiveDensityRadialResponse Signed.positiveCoupling = attractiveTowardPositiveSource
positiveDensityRadialResponse Signed.zeroCoupling = noNewtonianSourceResponse
positiveDensityRadialResponse Signed.negativeCoupling = repulsiveAwayFromPositiveSource

negativeGPositiveDensityIsRepulsiveInSignProbe :
  positiveDensityRadialResponse Signed.negativeCoupling
    ≡ repulsiveAwayFromPositiveSource
negativeGPositiveDensityIsRepulsiveInSignProbe = refl

positiveGPositiveDensityIsAttractiveInSignProbe :
  positiveDensityRadialResponse Signed.positiveCoupling
    ≡ attractiveTowardPositiveSource
positiveGPositiveDensityIsAttractiveInSignProbe = refl

------------------------------------------------------------------------
-- Introspective collision: the Poisson RHS sign does not identify whether G
-- or rho supplied the negative sign.
------------------------------------------------------------------------

data NewtonianSignFixture : Set where
  negativeGPositiveDensity : NewtonianSignFixture
  positiveGNegativeDensity : NewtonianSignFixture

fixtureCoupling : NewtonianSignFixture → Signed.CouplingSign
fixtureCoupling negativeGPositiveDensity = Signed.negativeCoupling
fixtureCoupling positiveGNegativeDensity = Signed.positiveCoupling

fixtureDensitySign : NewtonianSignFixture → Source.SourceSign
fixtureDensitySign negativeGPositiveDensity = Source.positiveSource
fixtureDensitySign positiveGNegativeDensity = Source.negativeSource

coarsePoissonObserver : NewtonianSignFixture → PoissonSourceOrientation
coarsePoissonObserver fixture =
  poissonSourceOrientation (fixtureCoupling fixture) (fixtureDensitySign fixture)

poissonSignCollision :
  coarsePoissonObserver negativeGPositiveDensity
    ≡ coarsePoissonObserver positiveGNegativeDensity
poissonSignCollision = refl

record RefinedNewtonianSignObserver : Set where
  constructor refined-newtonian-sign-observer
  field
    couplingSign : Signed.CouplingSign
    densitySign : Source.SourceSign

refinedNewtonianObserve : NewtonianSignFixture → RefinedNewtonianSignObserver
refinedNewtonianObserve fixture =
  refined-newtonian-sign-observer (fixtureCoupling fixture) (fixtureDensitySign fixture)

refinedNewtonianFixturesDistinct :
  refinedNewtonianObserve negativeGPositiveDensity
    ≡ refinedNewtonianObserve positiveGNegativeDensity → ⊥
refinedNewtonianFixturesDistinct ()

------------------------------------------------------------------------
-- Same-object reuse: the sign probe consumes literal objects and a literal
-- Poisson receipt from the existing WeakFieldNewtonianLimit carrier.
------------------------------------------------------------------------

record SignedNewtonianLimitProbe
    (law : Laws.EinsteinGravityLaw)
    (limit : Laws.WeakFieldNewtonianLimit law) : Set₁ where
  constructor signed-newtonian-limit-probe
  field
    couplingSign : Signed.CouplingSign
    densitySign : Source.SourceSign
    poissonOrientation : PoissonSourceOrientation
    poissonOrientationMatches :
      poissonOrientation ≡ poissonSourceOrientation couplingSign densitySign

    newtonianPotential :
      Laws.WeakFieldNewtonianLimit.NewtonianPotential limit
    sourceDensity :
      Laws.WeakFieldNewtonianLimit.SourceDensity limit
    poissonReceipt :
      Laws.WeakFieldNewtonianLimit.poissonEquation
        limit newtonianPotential sourceDensity

    SignedLimitAdequacy : Set
    signedLimitAdequacy : SignedLimitAdequacy

open SignedNewtonianLimitProbe public

record SignedNewtonianLimitBoundary : Set where
  constructor signed-newtonian-limit-boundary
  field
    negativeGPositiveDensityReversesNewtonianResponseInFrozenSignProbe : Bool
    poissonRHSSignDeterminesWhetherGOrDensityWasNegative : Bool
    negativeGEqualsNegativeDensity : Bool
    frozenPoissonSignProbeEqualsSolvedNegativeGNewtonianLimit : Bool
    negativeGAutomaticallyPreservesBoundOrbits : Bool
    negativeGAutomaticallyProvesAntigravity : Bool
    fullNegativeGLimitRequiresReSolvedPotentialAndTrajectories : Bool
    exactExistingPoissonReceiptRequired : Bool

canonicalSignedNewtonianLimitBoundary : SignedNewtonianLimitBoundary
canonicalSignedNewtonianLimitBoundary =
  signed-newtonian-limit-boundary true false false false false false true true
