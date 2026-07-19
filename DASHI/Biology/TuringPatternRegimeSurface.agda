module DASHI.Biology.TuringPatternRegimeSurface where

------------------------------------------------------------------------
-- Turing / reaction-diffusion regime taxonomy.
--
-- The diagrammatic "six stable states" is represented here as six stable
-- regimes plus an initial/noisy condition.  The final stable regime is the
-- stationary finite-wavelength instability usually called a Turing pattern.

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Regimes.

data TuringRegime : Set where
  initialNoisyCondition : TuringRegime
  uniformStationary : TuringRegime
  uniformOscillatory : TuringRegime
  stationaryShortWavelength : TuringRegime
  oscillatoryLongWavelength : TuringRegime
  oscillatoryFiniteWavelength : TuringRegime
  stationaryFiniteWavelengthTuring : TuringRegime

isTuringPatternRegime : TuringRegime → Set
isTuringPatternRegime stationaryFiniteWavelengthTuring = ⊤
isTuringPatternRegime _ = ⊥

------------------------------------------------------------------------
-- Tiny local truth types, to keep this surface independent of stdlib
-- propositions beyond equality.

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

------------------------------------------------------------------------
-- Variables and derivative role.

data TuringInputVariable : Set where
  activatorLevel : TuringInputVariable
  inhibitorLevel : TuringInputVariable
  activatorSpread : TuringInputVariable
  inhibitorSpread : TuringInputVariable
  reactionGain : TuringInputVariable
  inhibitionStrength : TuringInputVariable
  decayRate : TuringInputVariable
  noiseAmplitude : TuringInputVariable
  boundaryGeometry : TuringInputVariable
  anisotropyBias : TuringInputVariable
  wavelengthBand : TuringInputVariable
  oscillationFrequency : TuringInputVariable

-- Classical reaction-diffusion is normally first order in time and second
-- order in space through the Laplacian.  Higher-order jets may be useful as
-- model refinements, but they are not the core Turing operator.
data DerivativeRole : Set where
  firstOrderTimeEvolution : DerivativeRole
  secondOrderSpatialLaplacian : DerivativeRole
  higherOrderResidualJet : DerivativeRole

laplacianIsCoreDiffusionOperator : DerivativeRole
laplacianIsCoreDiffusionOperator = secondOrderSpatialLaplacian

------------------------------------------------------------------------
-- Pattern families named at the regime level, before visual projection.

data TuringPatternFamily : Set where
  frontFamily : TuringPatternFamily
  stripeFamily : TuringPatternFamily
  spotFamily : TuringPatternFamily
  hexagonFamily : TuringPatternFamily
  spiralFamily : TuringPatternFamily
  dissipativeSolitonFamily : TuringPatternFamily

record ReactionDiffusionSignature : Set₁ where
  constructor reactionDiffusionSignature
  field
    ActivatorField : Set
    InhibitorField : Set
    ReactionLaw : Set
    DiffusionLaw : Set
    BoundarySurface : Set

    firstOrderInTime : Set
    secondOrderInSpace : Set
    higherOrderTermsAreResidual : Set

record TuringPatternRegimeSurface : Set₁ where
  constructor turingPatternRegimeSurface
  field
    signature : ReactionDiffusionSignature
    regime : TuringRegime
    inputs : TuringInputVariable → Set
    selectedFamily : TuringPatternFamily

    wavelengthAmplification : Set
    wavelengthSuppression : Set
    finiteWavelengthWitness : Set
    stationaryWitness : Set

    notKluverFormByItself : Set
    notSemanticAuthority : Set

canonicalTuringRegimeIsFinalStableState :
  isTuringPatternRegime stationaryFiniteWavelengthTuring ≡ ⊤
canonicalTuringRegimeIsFinalStableState = refl
