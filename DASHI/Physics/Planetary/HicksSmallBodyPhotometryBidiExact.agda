module DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.FiniteObservationClosureBidiExact as Closure

-- Hicks's documented specialty was physical properties of comets/asteroids.
-- Representative work includes near-nucleus comet photometry and spectral /
-- photometric characterization of asteroids and vestoids.

data SmallBodyObservable : Set where broadbandFlux colourIndex phaseCurve rotationLightcurve spectrum thermalFlux radarShape : SmallBodyObservable

data PhysicalProperty : Set where rotationPeriod surfaceComposition albedo shape thermalInertia activityLevel : PhysicalProperty

record SmallBodyInferenceBoundary : Set where
  constructor small-body-inference-boundary
  field
    onePhotometricBandUniquelyDeterminesComposition : Bool
    onePhotometricBandUniquelyDeterminesCompositionIsFalse : onePhotometricBandUniquelyDeterminesComposition ≡ false
    lightcurveUniquelyDeterminesShapeWithoutGeometry : Bool
    lightcurveUniquelyDeterminesShapeWithoutGeometryIsFalse : lightcurveUniquelyDeterminesShapeWithoutGeometry ≡ false
    multiModalDataCanConstrainPhysicalModel : Bool
    multiModalDataCanConstrainPhysicalModelIsTrue : multiModalDataCanConstrainPhysicalModel ≡ true
    scienceTeamMembershipImpliesOwnershipOfMissionPhysics : Bool
    scienceTeamMembershipImpliesOwnershipOfMissionPhysicsIsFalse : scienceTeamMembershipImpliesOwnershipOfMissionPhysics ≡ false

canonicalSmallBodyInferenceBoundary : SmallBodyInferenceBoundary
canonicalSmallBodyInferenceBoundary = small-body-inference-boundary false refl false refl true refl false refl

hicksPhysicalModelReverse : Closure.ReverseClosureObligation
hicksPhysicalModelReverse = Closure.reverse-closure-obligation
  "comet / asteroid physical characterization"
  "photometric, spectral, thermal or radar observables"
  "viewing geometry plus scattering/thermal/shape forward model"
  "constrained physical properties such as rotation, shape, albedo or composition"
  "unique physical model from one observable channel"
