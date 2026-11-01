module DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection where

-- Turing-like pattern selection is represented as an instability-selected mode
-- geometry: local excitation, lateral inhibition, symmetry, and projection pick
-- a constrained family of finite-wavelength patterns.
record ReactionDiffusionModeSystem : Set₁ where
  field
    FieldState : Set
    Mode       : Set
    Symmetry   : Set
    Wavelength : Set
    Parameter  : Set

    evolve     : Parameter → FieldState → FieldState
    modeOf     : FieldState → Mode
    wavelength : Mode → Wavelength

    LocalExcitation   : Parameter → Set
    LateralInhibition : Parameter → Set
    FiniteWavelengthUnstable : Parameter → Mode → Set
    SymmetryAllowed   : Symmetry → Mode → Set
    StationaryPattern : Parameter → Mode → Set

record TuringModeSelectionWitness
  (R : ReactionDiffusionModeSystem) : Set₁ where
  open ReactionDiffusionModeSystem R
  field
    parameter : Parameter
    mode      : Mode
    symmetry  : Symmetry

    excitation : LocalExcitation parameter
    inhibition : LateralInhibition parameter
    finiteMode : FiniteWavelengthUnstable parameter mode
    allowed    : SymmetryAllowed symmetry mode
    stationary : StationaryPattern parameter mode

-- Observable repeating geometry may share an abstract mode-selection shape with
-- other domains without becoming identical in mechanism or meaning.
record ModeGeometryProjection
  (R : ReactionDiffusionModeSystem) : Set₁ where
  open ReactionDiffusionModeSystem R
  field
    ObservableGeometry : Set
    projectMode : Mode → ObservableGeometry
    ProjectionCompatible : Mode → Set

record ModeSelectionAuthorityBoundary : Set₁ where
  field
    turingPatternIsNotSemanticCode : Set
    sharedModeGeometryIsNotMechanismIdentity : Set
    visualSimilarityIsNotCausalEquivalence : Set
