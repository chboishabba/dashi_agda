module DASHI.Cognition.KlueverFormConstantProjection where

------------------------------------------------------------------------
-- Klüver form constants as perceptual projection classes.
--
-- These are not treated as semantic signs.  They are recorded as coarse
-- geometry classes that may arise when visual/retinotopic/cortical fields
-- project endogenous mode structure into the phenomenal visual field.

open import DASHI.Cognition.ModeGeometrySurface using (ModeGeometrySurface; modeGeometrySurface)

------------------------------------------------------------------------
-- The four classic form-constant families.

data KlueverForm : Set where
  latticeGrating : KlueverForm
  tunnelFunnel : KlueverForm
  spiral : KlueverForm
  radialCobweb : KlueverForm

------------------------------------------------------------------------
-- Visual carrier variables.  These are deliberately qualitative: the goal
-- is to keep a typed surface for later analytic/empirical refinement.

data VisualCarrierVariable : Set where
  retinalExcitation : VisualCarrierVariable
  corticalExcitation : VisualCarrierVariable
  lateralInhibition : VisualCarrierVariable
  orientationMapBias : VisualCarrierVariable
  retinotopicCoordinate : VisualCarrierVariable
  logPolarCoordinate : VisualCarrierVariable
  endogenousNoise : VisualCarrierVariable
  externalInputAttenuation : VisualCarrierVariable

record KlueverProjectionSurface : Set₁ where
  constructor klueverProjectionSurface
  field
    visualCarrier : Set
    corticalModeSpectrum : Set
    visualProjectionGeometry : Set
    observedForm : KlueverForm

    visualVariables : VisualCarrierVariable → Set
    endogenousModeSelection : Set
    formIsProjectedGeometry : Set

    notTuringRegimeByItself : Set
    noReverseRecoveryOfCarrier : Set
    noSemanticAuthority : Set
    noClinicalDiagnosis : Set
    noMysticalAuthority : Set

------------------------------------------------------------------------
-- Coarse geometry hints for classification.  These are intentionally many
-- to one and incomplete.

data KlueverGeometryHint : KlueverForm → Set where
  gridOrTilingHint : KlueverGeometryHint latticeGrating
  funnelDepthHint : KlueverGeometryHint tunnelFunnel
  angularPhaseHint : KlueverGeometryHint spiral
  radialSpokeHint : KlueverGeometryHint radialCobweb

record KlueverModeGeometryInstance : Set₁ where
  constructor klueverModeGeometryInstance
  field
    projectionSurface : KlueverProjectionSurface
    genericSurface : ModeGeometrySurface
