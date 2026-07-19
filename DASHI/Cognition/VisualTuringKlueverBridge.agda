module DASHI.Cognition.VisualTuringKlueverBridge where

------------------------------------------------------------------------
-- Lossy bridge:
--   Turing/excitable-media variables -> selected mode family ->
--   visual projection -> Klüver form constant.
--
-- The bridge is relational, not functional.  It prevents the wrong move
-- from an observed form back to a unique hidden tissue state or semantic
-- interpretation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Biology.TuringPatternRegimeSurface using
  ( TuringRegime
  ; stationaryFiniteWavelengthTuring
  ; TuringInputVariable
  ; TuringPatternFamily
  ; frontFamily
  ; stripeFamily
  ; spotFamily
  ; hexagonFamily
  ; spiralFamily
  ; dissipativeSolitonFamily
  ; DerivativeRole
  ; firstOrderTimeEvolution
  ; secondOrderSpatialLaplacian
  ; higherOrderResidualJet
  )
open import DASHI.Cognition.KlueverFormConstantProjection using
  ( KlueverForm
  ; latticeGrating
  ; tunnelFunnel
  ; spiral
  ; radialCobweb
  )

------------------------------------------------------------------------
-- Mode family may project as a Klüver class.  This relation is explicitly
-- partial and many-to-one.

data ProjectsAsKluever : TuringPatternFamily → KlueverForm → Set where
  stripesAsLattice : ProjectsAsKluever stripeFamily latticeGrating
  spotsAsLattice : ProjectsAsKluever spotFamily latticeGrating
  hexagonsAsLattice : ProjectsAsKluever hexagonFamily latticeGrating
  spiralAsSpiral : ProjectsAsKluever spiralFamily spiral
  frontAsTunnel : ProjectsAsKluever frontFamily tunnelFunnel
  frontAsRadial : ProjectsAsKluever frontFamily radialCobweb

record TuringToKlueverProjection : Set₁ where
  constructor turingToKlueverProjection
  field
    inputs : TuringInputVariable → Set
    regime : TuringRegime
    selectedFamily : TuringPatternFamily
    observedForm : KlueverForm

    projectionWitness : ProjectsAsKluever selectedFamily observedForm
    externalInputReduced : Set
    endogenousCarrierActive : Set
    modeSelectedByInstability : Set
    formIsVisualProjection : Set

    nonTotal : Set
    manyToOne : Set
    noReverseRecovery : Set
    noSemanticAuthority : Set
    noClinicalDiagnosis : Set

------------------------------------------------------------------------
-- Derivative/jet correction.
--
-- The Turing core is first order in time and second order in space.  Higher
-- order information belongs to a refinement jet or residual model, not to
-- the minimal reaction-diffusion operator.

record TuringDerivativeBoundary : Set where
  constructor turingDerivativeBoundary
  field
    timeRole : DerivativeRole
    spatialRole : DerivativeRole
    residualRole : DerivativeRole

    firstTimeAnchor : timeRole ≡ firstOrderTimeEvolution
    secondSpaceAnchor : spatialRole ≡ secondOrderSpatialLaplacian
    higherTermsResidualOnly : residualRole ≡ higherOrderResidualJet

canonicalTuringDerivativeBoundary : TuringDerivativeBoundary
canonicalTuringDerivativeBoundary =
  turingDerivativeBoundary
    firstOrderTimeEvolution
    secondOrderSpatialLaplacian
    higherOrderResidualJet
    refl
    refl
    refl

------------------------------------------------------------------------
-- The named observation from the discussion: final Turing-regime spatial
-- instability may project into a Klüver-style visual class, but the relation
-- is not identity.

record EndogenousVisualTuringProjection : Set₁ where
  constructor endogenousVisualTuringProjection
  field
    bridge : TuringToKlueverProjection
    derivativeBoundary : TuringDerivativeBoundary

    turingRegimeIsNotKluverForm : Set
    klueverFormDoesNotRecoverInputs : Set
    observableContactNotTruth : Set
