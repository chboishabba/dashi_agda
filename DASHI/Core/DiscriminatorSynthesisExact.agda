module DASHI.Core.DiscriminatorSynthesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice

------------------------------------------------------------------------
-- DISCRIMINATOR SYNTHESIS
--
-- Proof-search target for the question:
--   given a collision under the current observer, which declared experiment
--   bundle is the least-cost extension that separates the relevant states?
--
-- The construction is deterministic/proof-relevant.  It does not assume a
-- probability model, and cost is not epistemic truth.
------------------------------------------------------------------------

record ExperimentBundle (World : Set) : Set₁ where
  constructor experimentBundle
  field
    Observation : Set
    observe : World → Observation
    cost : Nat
    bundleReference : String
    calibrationReference : String

open ExperimentBundle public

record CurrentObserverCollision
    {World Existing : Set}
    (existing : World → Existing) : Set where
  constructor currentObserverCollision
  field
    left right : World
    collapsed : existing left ≡ existing right

open CurrentObserverCollision public

record BundleSeparates
    {World : Set}
    (bundle : ExperimentBundle World)
    (left right : World) : Set where
  constructor bundleSeparates
  field
    separates : observe bundle left ≡ observe bundle right → ⊥

open BundleSeparates public

record DiscriminatingLanguageExtension
    {World Existing : Set}
    (existing : World → Existing) : Set₁ where
  constructor discriminatingLanguageExtension
  field
    collision : CurrentObserverCollision existing
    extension : ExperimentBundle World
    extensionSeparates :
      BundleSeparates extension (left collision) (right collision)

open DiscriminatingLanguageExtension public

------------------------------------------------------------------------
-- Nuisance robustness.  A useful separator should not disappear merely under
-- the declared systematic/nuisance transformations the experiment claims to
-- tolerate.  This is shared-nuisance robustness; stronger stochastic/error
-- models can be layered separately.
------------------------------------------------------------------------

record NuisanceAction (World : Set) : Set₁ where
  constructor nuisanceAction
  field
    Nuisance : Set
    act : Nuisance → World → World
    nuisanceReference : Nuisance → String

open NuisanceAction public

record NuisanceRobustSeparator
    {World : Set}
    (bundle : ExperimentBundle World)
    (nuisance : NuisanceAction World)
    (Declared : Nuisance nuisance → Set)
    (left right : World) : Set₁ where
  constructor nuisanceRobustSeparator
  field
    separatesUnderDeclaredNuisance :
      (n : Nuisance nuisance) → Declared n →
      observe bundle (act nuisance n left)
      ≡ observe bundle (act nuisance n right) → ⊥

open NuisanceRobustSeparator public

------------------------------------------------------------------------
-- Minimality among a declared bundle library.
------------------------------------------------------------------------

record MinimalDiscriminator
    {World Existing : Set}
    (existing : World → Existing)
    (Declared : ExperimentBundle World → Set) : Set₁ where
  constructor minimalDiscriminator
  field
    collision : CurrentObserverCollision existing
    selected : ExperimentBundle World
    selectedDeclared : Declared selected
    selectedSeparates :
      BundleSeparates selected (left collision) (right collision)
    minimal :
      (alternative : ExperimentBundle World) →
      Declared alternative →
      BundleSeparates alternative (left collision) (right collision) →
      cost selected ≤ cost alternative
    synthesisReference : String

open MinimalDiscriminator public

------------------------------------------------------------------------
-- Perturb-and-measure discriminator over the existing coordinate-design owner.
------------------------------------------------------------------------

record ControlledCoordinateDiscriminator
    {World Control Value Dimension : Set}
    (design : Coordinate.ExperimentalCoordinateDesign
      World Control Value Dimension)
    (left right : World) : Set₁ where
  constructor controlledCoordinateDiscriminator
  field
    control : Control
    coordinate : Coordinate.Coordinate design
    separatesAfterControl :
      Coordinate.read design coordinate
        (Coordinate.applyControl design control left)
      ≡ Coordinate.read design coordinate
        (Coordinate.applyControl design control right) → ⊥
    controlAdmissibilityReference : String
    discriminationReference : String

open ControlledCoordinateDiscriminator public

------------------------------------------------------------------------
-- Bridge into the actionability-cost search.  An experiment bundle can be
-- treated as a measurement move without identifying its resolving proof.
------------------------------------------------------------------------

bundleInformationMove :
  ∀ {World} → ExperimentBundle World → Choice.InformationMove
bundleInformationMove bundle =
  Choice.informationMove
    Choice.takeMeasurement
    (cost bundle)
    (bundleReference bundle)
    (calibrationReference bundle)
    "declared experiment-bundle admissibility"

record ActionabilityResolvingDiscriminator
    {World : Set}
    (problem : Choice.ActionabilityProblem) : Set₁ where
  constructor actionabilityResolvingDiscriminator
  field
    bundle : ExperimentBundle World
    resolves :
      Choice.Resolves problem
        (bundleInformationMove bundle)
        (Choice.currentObstruction problem)
    resolutionReference : String

open ActionabilityResolvingDiscriminator public

record DiscriminatorSynthesisBoundary : Set where
  constructor discriminatorSynthesisBoundary
  field
    oneNewCoordinateAlwaysSeparatesAnyCollision : Bool
    oneNewCoordinateAlwaysSeparatesAnyCollisionIsFalse :
      oneNewCoordinateAlwaysSeparatesAnyCollision ≡ false

    nuisanceRobustnessNeedsDeclaredNuisanceLanguage : Bool
    nuisanceRobustnessNeedsDeclaredNuisanceLanguageIsTrue :
      nuisanceRobustnessNeedsDeclaredNuisanceLanguage ≡ true

    cheapestSeparatorIsAutomaticallyBestPhysicalTheory : Bool
    cheapestSeparatorIsAutomaticallyBestPhysicalTheoryIsFalse :
      cheapestSeparatorIsAutomaticallyBestPhysicalTheory ≡ false

    perturbAndMeasureCanCreateAUsefulDiscriminator : Bool
    perturbAndMeasureCanCreateAUsefulDiscriminatorIsTrue :
      perturbAndMeasureCanCreateAUsefulDiscriminator ≡ true

canonicalDiscriminatorSynthesisBoundary : DiscriminatorSynthesisBoundary
canonicalDiscriminatorSynthesisBoundary =
  discriminatorSynthesisBoundary false refl true refl false refl true refl
