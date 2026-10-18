module DASHI.Core.LawlikeRegularityCounterfactualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.WorldRepresentationSeparationExact as World
import DASHI.Core.ConsumerRelativeSymmetryRelevanceExact as Symmetry

------------------------------------------------------------------------
-- LAW-LIKE REGULARITY VS TRAJECTORY COINCIDENCE
--
-- A value seen on one trajectory is not yet a law-like invariant.  This module
-- treats "law-like for the declared test language" as preservation under a
-- declared family of admissible controls/counterfactual variations.
------------------------------------------------------------------------

record LawlikeRegularityTest
    {WorldState Control Value Dimension : Set}
    (design : Experiment.ExperimentalCoordinateDesign
      WorldState Control Value Dimension) : Set₁ where
  constructor lawlike-regularity-test
  field
    regularityCoordinate : Experiment.Coordinate design
    DeclaredControl : Control → Set
    invariant :
      Experiment.CoordinateInvariantUnder
        design regularityCoordinate DeclaredControl

open LawlikeRegularityTest public

data SingleTrajectoryImpliesLawlikePermission : Set where
data InvariantForSomeControlsImpliesUniversalLawPermission : Set where
data ConsumerInvarianceImpliesWorldOntologyPermission : Set where

singleTrajectoryDoesNotEstablishLawlikeRegularity :
  SingleTrajectoryImpliesLawlikePermission → ⊥
singleTrajectoryDoesNotEstablishLawlikeRegularity ()

declaredControlInvarianceDoesNotEstablishUniversalLaw :
  InvariantForSomeControlsImpliesUniversalLawPermission → ⊥
declaredControlInvarianceDoesNotEstablishUniversalLaw ()

consumerInvarianceDoesNotManufactureWorldOntology :
  ConsumerInvarianceImpliesWorldOntologyPermission → ⊥
consumerInvarianceDoesNotManufactureWorldOntology ()

------------------------------------------------------------------------
-- Finite witness:
-- one coordinate varies under control while a second coordinate is invariant.
-- This separates state/trajectory change from regularity preservation.
------------------------------------------------------------------------

data DemoWorld : Set where
  worldLow : DemoWorld
  worldHigh : DemoWorld

data DemoControl : Set where
  flipState : DemoControl

data DemoValue : Set where
  lowValue : DemoValue
  highValue : DemoValue
  invariantValue : DemoValue

data DemoDimension : Set where
  stateDimension : DemoDimension
  regularityDimension : DemoDimension

data DemoCoordinate : Set where
  changingCoordinate : DemoCoordinate
  regularityCoordinate : DemoCoordinate

demoDesign :
  Experiment.ExperimentalCoordinateDesign
    DemoWorld DemoControl DemoValue DemoDimension
demoDesign =
  Experiment.experimentalCoordinateDesign
    DemoCoordinate
    role
    dimension
    read
    apply
    (λ c → "counterfactual regularity fixture coordinate")
    (λ d → "counterfactual regularity fixture dimension")
    (λ c → "finite exact fixture")
    (λ control → "finite state-flip control")
  where
    role : DemoCoordinate → Experiment.CoordinateRole
    role changingCoordinate = Experiment.controlledInput
    role regularityCoordinate = Experiment.referenceInvariant

    dimension : DemoCoordinate → DemoDimension
    dimension changingCoordinate = stateDimension
    dimension regularityCoordinate = regularityDimension

    read : DemoCoordinate → DemoWorld → DemoValue
    read changingCoordinate worldLow = lowValue
    read changingCoordinate worldHigh = highValue
    read regularityCoordinate worldLow = invariantValue
    read regularityCoordinate worldHigh = invariantValue

    apply : DemoControl → DemoWorld → DemoWorld
    apply flipState worldLow = worldHigh
    apply flipState worldHigh = worldLow

DeclaredDemoControl : DemoControl → Set
DeclaredDemoControl flipState = ⊤

demoRegularityInvariant :
  Experiment.CoordinateInvariantUnder
    demoDesign regularityCoordinate DeclaredDemoControl
demoRegularityInvariant =
  Experiment.coordinateInvariantUnder preserved
  where
    preserved :
      (control : DemoControl) →
      DeclaredDemoControl control →
      (world : DemoWorld) →
      Experiment.read demoDesign regularityCoordinate
        (Experiment.applyControl demoDesign control world)
      ≡ Experiment.read demoDesign regularityCoordinate world
    preserved flipState tt worldLow = refl
    preserved flipState tt worldHigh = refl

demoStateActuallyChanges :
  Experiment.CoordinateModifiableBy demoDesign changingCoordinate
demoStateActuallyChanges =
  Experiment.coordinateModifiableBy flipState worldLow differs
  where
    differs :
      Experiment.read demoDesign changingCoordinate
        (Experiment.applyControl demoDesign flipState worldLow)
      ≡ Experiment.read demoDesign changingCoordinate worldLow → ⊥
    differs ()

demoLawlikeTest : LawlikeRegularityTest demoDesign
demoLawlikeTest =
  lawlike-regularity-test
    regularityCoordinate
    DeclaredDemoControl
    demoRegularityInvariant

worldBoundary : World.WorldRepresentationBoundary
worldBoundary = World.canonicalWorldRepresentationBoundary

symmetryBoundary : Symmetry.ConsumerRelativeSymmetryBoundary
symmetryBoundary = Symmetry.canonicalConsumerRelativeSymmetryBoundary

record LawlikeRegularityBoundary : Set where
  constructor lawlike-regularity-boundary
  field
    lawlikeStatusRequiresDeclaredVariationFamily : Bool
    lawlikeStatusRequiresDeclaredVariationFamilyIsTrue :
      lawlikeStatusRequiresDeclaredVariationFamily ≡ true
    stateMayChangeWhileRegularityCoordinateIsPreserved : Bool
    stateMayChangeWhileRegularityCoordinateIsPreservedIsTrue :
      stateMayChangeWhileRegularityCoordinateIsPreserved ≡ true
    oneObservedTrajectoryEstablishesUniversalLaw : Bool
    oneObservedTrajectoryEstablishesUniversalLawIsFalse :
      oneObservedTrajectoryEstablishesUniversalLaw ≡ false
    finiteControlInvarianceEstablishesMetaphysicalNecessity : Bool
    finiteControlInvarianceEstablishesMetaphysicalNecessityIsFalse :
      finiteControlInvarianceEstablishesMetaphysicalNecessity ≡ false

open LawlikeRegularityBoundary public

canonicalLawlikeRegularityBoundary : LawlikeRegularityBoundary
canonicalLawlikeRegularityBoundary =
  lawlike-regularity-boundary true refl true refl false refl false refl
