module DASHI.Cognition.VisualPatternModeGeometryBundle where

------------------------------------------------------------------------
-- Aggregate surface for the Turing -> mode-selection -> visual projection
-- lane.  This bundle collects actual relations and boundary witnesses; it
-- does not assert an empirical brain model or promote a clinical claim.

open import DASHI.Cognition.ModeGeometrySurface using
  ( ModeGeometrySurface
  ; ObservableContactGeometryBoundary
  ; ModeGeometryLane
  )
open import DASHI.Biology.TuringPatternRegimeSurface using
  ( TuringPatternRegimeSurface
  ; TuringRegime
  ; stationaryFiniteWavelengthTuring
  ; isTuringPatternRegime
  ; ⊤
  ; tt
  )
open import DASHI.Cognition.KlueverFormConstantProjection using
  ( KlueverProjectionSurface
  ; KlueverModeGeometryInstance
  )
open import DASHI.Cognition.VisualTuringKlueverBridge using
  ( TuringToKlueverProjection
  ; TuringDerivativeBoundary
  ; canonicalTuringDerivativeBoundary
  ; EndogenousVisualTuringProjection
  )
open import DASHI.Cognition.PerceptualModeJet using
  ( PerceptualModeJet
  ; PerceptualModeJetBoundary
  )
open import DASHI.Cognition.ModeSelectionToProjectionLaw using
  ( ModeSelectionToProjectionLaw
  ; ManyToOneLatticeWitness
  ; canonicalManyToOneLatticeWitness
  ; NonTotalProjectionWitness
  ; canonicalNonTotalProjectionWitness
  )

------------------------------------------------------------------------
-- Stable-regime anchor.

finalTuringRegimeWitness :
  isTuringPatternRegime stationaryFiniteWavelengthTuring
finalTuringRegimeWitness = tt

------------------------------------------------------------------------
-- Reviewable assembly.  Empirical carrier laws and projection instances
-- remain explicit inputs; the structural derivative, many-to-one, and
-- non-totality witnesses are already closed.

record VisualPatternModeGeometryBundle : Set₁ where
  constructor visualPatternModeGeometryBundle
  field
    genericModeSurface : ModeGeometrySurface
    contactBoundary : ObservableContactGeometryBoundary
    turingSurface : TuringPatternRegimeSurface
    klueverSurface : KlueverProjectionSurface
    klueverInstance : KlueverModeGeometryInstance
    projectionBridge : TuringToKlueverProjection
    projectionLaw : ModeSelectionToProjectionLaw
    perceptualJet : PerceptualModeJet
    perceptualJetBoundary : PerceptualModeJetBoundary

    derivativeBoundary : TuringDerivativeBoundary
    manyToOneWitness : ManyToOneLatticeWitness
    nonTotalWitness : NonTotalProjectionWitness

    noClinicalPromotion : Set
    noSemanticPromotion : Set
    noMysticalPromotion : Set
    noExactInverseRecovery : Set

record VisualPatternStructuralClosure : Set where
  constructor visualPatternStructuralClosure
  field
    finalRegimeWitness :
      isTuringPatternRegime stationaryFiniteWavelengthTuring
    derivativeBoundary : TuringDerivativeBoundary
    manyToOneWitness : ManyToOneLatticeWitness
    nonTotalWitness : NonTotalProjectionWitness

canonicalVisualPatternStructuralClosure : VisualPatternStructuralClosure
canonicalVisualPatternStructuralClosure =
  visualPatternStructuralClosure
    finalTuringRegimeWitness
    canonicalTuringDerivativeBoundary
    canonicalManyToOneLatticeWitness
    canonicalNonTotalProjectionWitness
