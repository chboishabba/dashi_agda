module DASHI.Core.ExperimentalCoordinateDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EXPERIMENTAL COORDINATE DESIGN
--
-- Repository-native abstraction for the recurring question: which coordinates
-- of a system are fixed reference structure, which may be deliberately varied,
-- which are observed, which are nuisance/systematic coordinates, and which are
-- derived discriminators constructed from measurements.
--
-- This is intentionally not a claim that an experiment may "invent physical
-- dimensions".  A new experimental coordinate enlarges the information/
-- observation language only when its derivation or calibration is supplied.
------------------------------------------------------------------------

data CoordinateRole : Set where
  referenceInvariant
  controlledInput
  measuredObservable
  nuisanceCoordinate
  derivedDiscriminator
  : CoordinateRole

record ExperimentalCoordinateDesign
    (World Control Value Dimension : Set) : Set₁ where
  constructor experimentalCoordinateDesign
  field
    Coordinate : Set
    role : Coordinate → CoordinateRole
    dimension : Coordinate → Dimension
    read : Coordinate → World → Value
    applyControl : Control → World → World

    coordinateReference : Coordinate → String
    dimensionReference : Coordinate → String
    calibrationOrDerivationReference : Coordinate → String
    controlReference : Control → String

open ExperimentalCoordinateDesign public

------------------------------------------------------------------------
-- Invariants are relative to a declared family of controls.  Nothing in the
-- carrier asserts that every coordinate is invariant or controllable.
------------------------------------------------------------------------

record CoordinateInvariantUnder
    {World Control Value Dimension : Set}
    (design : ExperimentalCoordinateDesign World Control Value Dimension)
    (coordinate : Coordinate design)
    (DeclaredControl : Control → Set) : Set₁ where
  constructor coordinateInvariantUnder
  field
    preserved :
      (control : Control) → DeclaredControl control → (world : World) →
      read design coordinate (applyControl design control world)
      ≡ read design coordinate world

open CoordinateInvariantUnder public

------------------------------------------------------------------------
-- A control witness says a coordinate can actually be changed by some admitted
-- intervention.  This is deliberately existential and does not imply that the
-- coordinate is safe, ethical, technically feasible, or authority-approved to
-- manipulate in every application.
------------------------------------------------------------------------

record CoordinateModifiableBy
    {World Control Value Dimension : Set}
    (design : ExperimentalCoordinateDesign World Control Value Dimension)
    (coordinate : Coordinate design) : Set₁ where
  constructor coordinateModifiableBy
  field
    control : Control
    world : World
    changesCoordinate :
      read design coordinate (applyControl design control world)
      ≡ read design coordinate world → ⊥

open CoordinateModifiableBy public

------------------------------------------------------------------------
-- Derived coordinates may add discriminatory information, but their provenance
-- is explicit.  They do not create a new SI/base physical dimension merely by
-- being useful features of an experiment.
------------------------------------------------------------------------

record DerivedCoordinateReceipt
    {World Control Value Dimension : Set}
    (design : ExperimentalCoordinateDesign World Control Value Dimension)
    (coordinate : Coordinate design) : Set₁ where
  constructor derivedCoordinateReceipt
  field
    isDerived : role design coordinate ≡ derivedDiscriminator
    SourceCoordinate : Set
    source : SourceCoordinate → Coordinate design
    derive : (SourceCoordinate → Value) → Value
    derivationReference : String
    validationReference : String

open DerivedCoordinateReceipt public

------------------------------------------------------------------------
-- Informational-language extension.  A new coordinate is valuable when two
-- currently indistinguishable worlds are separated by reading it.  This is an
-- increase in observational resolution, not automatically a new physical
-- dimension.
------------------------------------------------------------------------

record CoordinateSeparatesCollision
    {World Control Value Dimension ExistingCode : Set}
    (design : ExperimentalCoordinateDesign World Control Value Dimension)
    (existing : World → ExistingCode) : Set₁ where
  constructor coordinateSeparatesCollision
  field
    coordinate : Coordinate design
    left right : World
    currentlyCollapsed : existing left ≡ existing right
    coordinateSeparates :
      read design coordinate left ≡ read design coordinate right → ⊥

open CoordinateSeparatesCollision public

record ExperimentalCoordinateBoundary : Set where
  constructor experimentalCoordinateBoundary
  field
    allCoordinatesMustBeSymmetriesOrInvariants : Bool
    allCoordinatesMustBeSymmetriesOrInvariantsIsFalse :
      allCoordinatesMustBeSymmetriesOrInvariants ≡ false

    controlledCoordinateMayBeVariedWithoutAuthority : Bool
    controlledCoordinateMayBeVariedWithoutAuthorityIsFalse :
      controlledCoordinateMayBeVariedWithoutAuthority ≡ false

    derivedFeatureAutomaticallyCreatesPhysicalDimension : Bool
    derivedFeatureAutomaticallyCreatesPhysicalDimensionIsFalse :
      derivedFeatureAutomaticallyCreatesPhysicalDimension ≡ false

    addedCoordinateCanIncreaseObservationalResolution : Bool
    addedCoordinateCanIncreaseObservationalResolutionIsTrue :
      addedCoordinateCanIncreaseObservationalResolution ≡ true

    invariantStatusIsRelativeToDeclaredControlLanguage : Bool
    invariantStatusIsRelativeToDeclaredControlLanguageIsTrue :
      invariantStatusIsRelativeToDeclaredControlLanguage ≡ true

canonicalExperimentalCoordinateBoundary : ExperimentalCoordinateBoundary
canonicalExperimentalCoordinateBoundary =
  experimentalCoordinateBoundary
    false refl false refl false refl true refl true refl
