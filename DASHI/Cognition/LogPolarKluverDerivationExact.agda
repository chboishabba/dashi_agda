module DASHI.Cognition.LogPolarKluverDerivationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.LogPolarRetinotopyBridge as LogPolar
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as Sources
import DASHI.Cognition.KlueverFormConstantProjection as Kluver
import DASHI.Cognition.CorticalLogPolarProjectionGeometry as Geometry

------------------------------------------------------------------------
-- DASHI EXTENSION
--
-- The external sources motivate the retinocortical/log-polar approximation
-- and symmetry-selected cortical modes.  The finite derivations below are
-- repository-native exact witnesses built from the pre-existing finite
-- LogPolarRetinotopyBridge.  They are not statements attributed to Schwartz,
-- Grusser, Ermentrout/Cowan, Bressloff et al., or Hadjikhani et al.
------------------------------------------------------------------------

sourceAtlas : DASHI.Core.AttributedSourceCore.AttributedSourceAtlas
sourceAtlas = Sources.canonicalKluverLogPolar5HT2AAtlas

------------------------------------------------------------------------
-- Finite log-polar spiral witness.
--
-- A simultaneous multiplicative radial step and angular rotation becomes a
-- diagonal additive trajectory in the finite cortical chart:
--
--   (r,theta) = (1,0) -> (2,1) -> (4,2)
--   log-polar    (0,0) -> (1,1) -> (2,2)
--
-- Combined with the already-existing qualitative cortical projection relation
-- angularPhaseDrift -> Kluever spiral, this provides an exact composition
-- witness without pretending the finite three-point carrier is a fitted V1
-- coordinate system.

record FiniteLogPolarSpiralDerivation : Set where
  constructor finiteLogPolarSpiralDerivation
  field
    start : LogPolar.PolarSample
    second : LogPolar.PolarSample
    third : LogPolar.PolarSample

    secondIsSpiralStep :
      second ≡ LogPolar.spiralStep start

    thirdIsSpiralStep :
      third ≡ LogPolar.spiralStep second

    secondMapsToDiagonalOne :
      LogPolar.retinocorticalMap second
      ≡
      LogPolar.corticalSample 1 1

    thirdMapsToDiagonalTwo :
      LogPolar.retinocorticalMap third
      ≡
      LogPolar.corticalSample 2 2

    phaseFeature : Geometry.VisualModeFeature
    phaseFeatureIsAngularDrift :
      phaseFeature ≡ Geometry.angularPhaseDrift

    projectedForm : Kluver.KlueverForm
    projectedFormIsSpiral :
      projectedForm ≡ Kluver.spiral

    featureProjectsAsSpiral :
      Geometry.FeatureProjectsAs phaseFeature projectedForm

open FiniteLogPolarSpiralDerivation public

canonicalFiniteLogPolarSpiralDerivation :
  FiniteLogPolarSpiralDerivation
canonicalFiniteLogPolarSpiralDerivation =
  finiteLogPolarSpiralDerivation
    LogPolar.spiralStart
    LogPolar.spiralSecond
    LogPolar.spiralThird
    refl
    refl
    LogPolar.spiralSecondMapsToDiagonalOne
    LogPolar.spiralThirdMapsToDiagonalTwo
    Geometry.angularPhaseDrift
    refl
    Kluver.spiral
    refl
    Geometry.angularDriftAsSpiral

------------------------------------------------------------------------
-- Finite cortical-magnification witness.
--
-- Equal unit translations in log-radius correspond here to unequal physical
-- radius increments:
--
--   radius 1 -> 2 : visual increment 1, cortical increment 1
--   radius 2 -> 4 : visual increment 2, cortical increment 1
--
-- This is a discrete structural analogue of the source-side migraine /
-- cortical-magnification argument.  It is not a measured speed law.

data RadialTransition : Set where
  oneToTwo : RadialTransition
  twoToFour : RadialTransition

visualRadiusIncrement : RadialTransition → Nat
visualRadiusIncrement oneToTwo = 1
visualRadiusIncrement twoToFour = 2

corticalLogRadiusIncrement : RadialTransition → Nat
corticalLogRadiusIncrement oneToTwo = 1
corticalLogRadiusIncrement twoToFour = 1

equalCorticalSteps :
  corticalLogRadiusIncrement oneToTwo
  ≡
  corticalLogRadiusIncrement twoToFour
equalCorticalSteps = refl

visualStepsDiffer :
  visualRadiusIncrement oneToTwo
  ≡
  visualRadiusIncrement twoToFour
  →
  ⊥
visualStepsDiffer ()

firstDoublingIsCorticalUnitTranslation :
  LogPolar.logRadiusCode
    (LogPolar.doubleRadius LogPolar.radiusOne)
  ≡
  suc (LogPolar.logRadiusCode LogPolar.radiusOne)
firstDoublingIsCorticalUnitTranslation =
  LogPolar.doublingAtRadiusOneIsUnitTranslation

secondDoublingIsCorticalUnitTranslation :
  LogPolar.logRadiusCode
    (LogPolar.doubleRadius LogPolar.radiusTwo)
  ≡
  suc (LogPolar.logRadiusCode LogPolar.radiusTwo)
secondDoublingIsCorticalUnitTranslation =
  LogPolar.doublingAtRadiusTwoIsUnitTranslation

record FiniteCorticalMagnificationWitness : Set where
  constructor finiteCorticalMagnificationWitness
  field
    sameCorticalIncrement :
      corticalLogRadiusIncrement oneToTwo
      ≡
      corticalLogRadiusIncrement twoToFour

    unequalVisualIncrement :
      visualRadiusIncrement oneToTwo
      ≡
      visualRadiusIncrement twoToFour
      →
      ⊥

    firstLogTranslation :
      LogPolar.logRadiusCode
        (LogPolar.doubleRadius LogPolar.radiusOne)
      ≡
      suc (LogPolar.logRadiusCode LogPolar.radiusOne)

    secondLogTranslation :
      LogPolar.logRadiusCode
        (LogPolar.doubleRadius LogPolar.radiusTwo)
      ≡
      suc (LogPolar.logRadiusCode LogPolar.radiusTwo)

open FiniteCorticalMagnificationWitness public

canonicalFiniteCorticalMagnificationWitness :
  FiniteCorticalMagnificationWitness
canonicalFiniteCorticalMagnificationWitness =
  finiteCorticalMagnificationWitness
    equalCorticalSteps
    visualStepsDiffer
    firstDoublingIsCorticalUnitTranslation
    secondDoublingIsCorticalUnitTranslation

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record LogPolarKluverAuthorityBoundary : Set where
  constructor logPolarKluverAuthorityBoundary
  field
    finiteLogPolarCompositionProved : Bool
    finiteLogPolarCompositionProvedIsTrue :
      finiteLogPolarCompositionProved ≡ true

    finiteMagnificationAnalogueProved : Bool
    finiteMagnificationAnalogueProvedIsTrue :
      finiteMagnificationAnalogueProved ≡ true

    exactHumanV1MapRecovered : Bool
    exactHumanV1MapRecoveredIsFalse :
      exactHumanV1MapRecovered ≡ false

    migraineAndPsychedelicMechanismIdentical : Bool
    migraineAndPsychedelicMechanismIdenticalIsFalse :
      migraineAndPsychedelicMechanismIdentical ≡ false

    everyKluverFormUniquelyInvertsToCorticalState : Bool
    everyKluverFormUniquelyInvertsToCorticalStateIsFalse :
      everyKluverFormUniquelyInvertsToCorticalState ≡ false

open LogPolarKluverAuthorityBoundary public

canonicalLogPolarKluverAuthorityBoundary :
  LogPolarKluverAuthorityBoundary
canonicalLogPolarKluverAuthorityBoundary =
  logPolarKluverAuthorityBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
