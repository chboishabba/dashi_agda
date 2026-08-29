module DASHI.Core.DiscriminatorSynthesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.PredictionEnvelopeExact as Envelope

------------------------------------------------------------------------
-- DISCRIMINATOR SYNTHESIS
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

joinedObservation :
  ∀ {World Existing}
    (existing : World → Existing) →
    (bundle : ExperimentBundle World) →
  World → Existing × Observation bundle
joinedObservation existing bundle world =
  existing world , observe bundle world

extensionJoinSeparates :
  ∀ {World Existing}
    {existing : World → Existing}
    (extension : DiscriminatingLanguageExtension existing) →
  joinedObservation existing (DiscriminatingLanguageExtension.extension extension)
    (left (collision extension))
  ≡ joinedObservation existing (DiscriminatingLanguageExtension.extension extension)
    (right (collision extension)) → ⊥
extensionJoinSeparates extension same =
  separates (extensionSeparates extension) (cong proj₂ same)

------------------------------------------------------------------------
-- Prospective consumer closure.
--
-- Pairwise separation is not enough when many live hypotheses remain.  A
-- prospective measurement is consumer-closing when, for every currently
-- compatible true state, observing that state's measurement value makes the
-- declared downstream consumer point-identifiable on the refined fibre.
------------------------------------------------------------------------

ProspectivelyClosesConsumer :
  ∀ {Evidence World Prediction : Set} →
  Envelope.Compatible Evidence World →
  (World → Prediction) →
  ExperimentBundle World → Set₁
ProspectivelyClosesConsumer compatible consumer bundle =
  ∀ evidence witness →
  compatible evidence witness →
  Envelope.MeasurementClosesEnvelope
    compatible
    (observe bundle)
    consumer
    (evidence , observe bundle witness)

record MinimalConsumerClosingBundle
    {Evidence World Prediction : Set}
    (compatible : Envelope.Compatible Evidence World)
    (consumer : World → Prediction)
    (Declared : ExperimentBundle World → Set) : Set₁ where
  constructor minimalConsumerClosingBundle
  field
    selected : ExperimentBundle World
    selectedDeclared : Declared selected
    selectedCloses : ProspectivelyClosesConsumer compatible consumer selected
    minimal :
      (alternative : ExperimentBundle World) →
      Declared alternative →
      ProspectivelyClosesConsumer compatible consumer alternative →
      cost selected ≤ cost alternative
    consumerClosureReference : String

open MinimalConsumerClosingBundle public

------------------------------------------------------------------------
-- Nuisance robustness.
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
-- Optional symmetry compatibility.
------------------------------------------------------------------------

record SymmetryInvariantBundle
    {World : Set}
    (bundle : ExperimentBundle World)
    (symmetry : Reduction.SymmetryAction World) : Set₁ where
  constructor symmetryInvariantBundle
  field
    invariant :
      (g : Reduction.Symmetry symmetry) (world : World) →
      observe bundle (Reduction.act symmetry g world) ≡ observe bundle world
    symmetryReference : String

open SymmetryInvariantBundle public

------------------------------------------------------------------------
-- Minimality for one explicit collision.
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
-- Perturb-and-measure discriminator.
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
-- Bridge into actionability-cost search.
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

    pairwiseSeparationAutomaticallyClosesWholeConsumerFibre : Bool
    pairwiseSeparationAutomaticallyClosesWholeConsumerFibreIsFalse :
      pairwiseSeparationAutomaticallyClosesWholeConsumerFibre ≡ false

    prospectiveClosureCanTargetDecisionRatherThanWorldIdentity : Bool
    prospectiveClosureCanTargetDecisionRatherThanWorldIdentityIsTrue :
      prospectiveClosureCanTargetDecisionRatherThanWorldIdentity ≡ true

    nuisanceRobustnessNeedsDeclaredNuisanceLanguage : Bool
    nuisanceRobustnessNeedsDeclaredNuisanceLanguageIsTrue :
      nuisanceRobustnessNeedsDeclaredNuisanceLanguage ≡ true

    cheapestSeparatorIsAutomaticallyBestPhysicalTheory : Bool
    cheapestSeparatorIsAutomaticallyBestPhysicalTheoryIsFalse :
      cheapestSeparatorIsAutomaticallyBestPhysicalTheory ≡ false

    perturbAndMeasureCanCreateAUsefulDiscriminator : Bool
    perturbAndMeasureCanCreateAUsefulDiscriminatorIsTrue :
      perturbAndMeasureCanCreateAUsefulDiscriminator ≡ true

    symmetryCompatibilityIsRequiredForEveryExperiment : Bool
    symmetryCompatibilityIsRequiredForEveryExperimentIsFalse :
      symmetryCompatibilityIsRequiredForEveryExperiment ≡ false

canonicalDiscriminatorSynthesisBoundary : DiscriminatorSynthesisBoundary
canonicalDiscriminatorSynthesisBoundary =
  discriminatorSynthesisBoundary
    false refl false refl true refl true refl false refl true refl false refl
