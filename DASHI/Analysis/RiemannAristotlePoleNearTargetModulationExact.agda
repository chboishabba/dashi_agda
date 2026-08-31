module DASHI.Analysis.RiemannAristotlePoleNearTargetModulationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil

------------------------------------------------------------------------
-- EXPLICIT-FORMULA ROUTE: TARGET MODULATION / WINDOW INFRASTRUCTURE
--
-- The canonical WeilTestSpace owns admissible tests and transforms, but no
-- target-ordinate modulation or finite near-window operation.  The RH explicit-
-- formula route therefore needs an explicit constructor for f_{t,J} rather than
-- silently assuming translation/modulation closure.
------------------------------------------------------------------------

record PoleNearTargetModulation
    (space : Weil.WeilTestSpace) : Set₁ where
  open Weil.WeilTestSpace space
  constructor pole-near-target-modulation
  field
    Target Cutoff : Set

    basePoleTest : Test
    basePoleAdmissible : admissible basePoleTest

    modulateAt : Target → Test → Test
    windowAt : Cutoff → Test → Test

    target : Target
    cutoff : Cutoff

    modulatedPoleTest : Test
    modulatedPoleTestIsConstruction :
      modulatedPoleTest ≡ windowAt cutoff (modulateAt target basePoleTest)

    modulatedPoleAdmissible : admissible modulatedPoleTest

    targetRelativePhaseOwned : Set
    poleTaperCarrierOwned : Set
    nearWindowOwned : Set
    modulationReference : String

open PoleNearTargetModulation public

record ModulationSpectralIdentification
    (space : Weil.WeilTestSpace)
    (m : PoleNearTargetModulation space) : Set₁ where
  open Weil.WeilTestSpace space
  constructor modulation-spectral-identification
  field
    spectralValue : Scalar
    sameOrdinateCluster : Scalar
    finitePoleNearSigned : Scalar
    farZeroRemainder : Scalar

    _⊕_ : Scalar → Scalar → Scalar

    spectralIsClusterNearFar :
      spectralValue ≡
      (sameOrdinateCluster ⊕ (finitePoleNearSigned ⊕ farZeroRemainder))

    identifiesActualSpectralForm : Set
    preservesTargetRelativeGap : Set
    preservesMultiplicity : Set
    preservesNearOffFinset : Set
    identificationReference : String

open ModulationSpectralIdentification public

record PoleNearTargetModulationBoundary : Set where
  constructor pole-near-target-modulation-boundary
  field
    genericWeilTestSpaceAlreadyOwnsTargetModulation : Bool
    genericWeilTestSpaceAlreadyOwnsTargetModulationIsFalse :
      genericWeilTestSpaceAlreadyOwnsTargetModulation ≡ false

    admissibilityOfTargetWindowMustBeProved : Bool
    admissibilityOfTargetWindowMustBeProvedIsTrue :
      admissibilityOfTargetWindowMustBeProved ≡ true

    exactSpectralWindowIdentityMustBeProved : Bool
    exactSpectralWindowIdentityMustBeProvedIsTrue :
      exactSpectralWindowIdentityMustBeProved ≡ true

    targetWindowConstructionClosed : Bool
    targetWindowConstructionClosedIsFalse : targetWindowConstructionClosed ≡ false

    nextTheorem : String

canonicalPoleNearTargetModulationBoundary : PoleNearTargetModulationBoundary
canonicalPoleNearTargetModulationBoundary =
  pole-near-target-modulation-boundary
    false refl
    true refl
    true refl
    false refl
    "Construct the actual high-ordinate pole test f_{t,J} by a source-native target modulation/window operation, prove its Weil admissibility, and identify its spectral zero form exactly with same-ordinate cluster + finite reflection-paired pole-near response + far zero remainder."
