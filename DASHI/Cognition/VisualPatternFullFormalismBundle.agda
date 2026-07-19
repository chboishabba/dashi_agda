module DASHI.Cognition.VisualPatternFullFormalismBundle where

------------------------------------------------------------------------
-- Full discussion-level aggregate.
--
-- This bundle collects the distinct layers without identifying them:
--
--   coupled carrier
--     -> instability-selected mode family
--     -> derivative / jet description
--     -> cortical projection geometry
--     -> phosphene or Klüver observation
--
-- together with the separate Eisenstein/Turing structural-analogy boundary.

open import DASHI.Biology.CoupledElectrochemicalPatternCarrier using
  ( CoupledCarrierBoundary )
open import DASHI.Biology.TuringPatternRegimeSurface using
  ( TuringPatternRegimeSurface )
open import DASHI.Cognition.PerceptualModeJet using
  ( PerceptualModeJetBoundary )
open import DASHI.Cognition.CorticalLogPolarProjectionGeometry using
  ( CorticalModeProjection )
open import DASHI.Cognition.EndogenousPhospheneObservationBridge using
  ( PhospheneProjectionWitness )
open import DASHI.Cognition.VisualTuringKlueverBridge using
  ( EndogenousVisualTuringProjection )
open import DASHI.Cognition.ModeSelectionToProjectionLaw using
  ( ManyToOneProjectionWitness
  ; NonTotalProjectionWitness
  )
open import DASHI.Analysis.EisensteinTuringModeAnalogyBoundary using
  ( EisensteinTuringAnalogyBoundary )

record VisualPatternFullFormalismBundle : Set₁ where
  constructor visualPatternFullFormalismBundle
  field
    coupledCarrierBoundary : CoupledCarrierBoundary
    turingRegimeSurface : TuringPatternRegimeSurface
    perceptualJetBoundary : PerceptualModeJetBoundary
    corticalProjection : CorticalModeProjection
    phospheneObservation : PhospheneProjectionWitness
    turingKlueverBoundary : EndogenousVisualTuringProjection

    manyToOneWitness : ManyToOneProjectionWitness
    nonTotalWitness : NonTotalProjectionWitness
    eisensteinAnalogyBoundary : EisensteinTuringAnalogyBoundary

    carrierModeProjectionLayersRemainDistinct : Set
    externalAttenuationDoesNotEraseCarrier : Set
    selectedModeDoesNotUniquelyFixPercept : Set
    perceptDoesNotRecoverCarrier : Set

    noSemanticAuthority : Set
    noClinicalDiagnosis : Set
    noMysticalAuthority : Set
    noArithmeticPerceptIdentity : Set

------------------------------------------------------------------------
-- Promotion status remains explicitly candidate-only until analytic and
-- empirical hypotheses are supplied and separately discharged.

data VisualPatternPromotionStatus : Set where
  structuralCandidateOnly : VisualPatternPromotionStatus
  analyticBridgeOutstanding : VisualPatternPromotionStatus
  empiricalCalibrationOutstanding : VisualPatternPromotionStatus

record VisualPatternPromotionBoundary : Set₁ where
  constructor visualPatternPromotionBoundary
  field
    bundle : VisualPatternFullFormalismBundle
    structuralStatus : VisualPatternPromotionStatus
    analyticStatus : VisualPatternPromotionStatus
    empiricalStatus : VisualPatternPromotionStatus

    structuralAnchor : structuralStatus ≡ structuralCandidateOnly
    analyticAnchor : analyticStatus ≡ analyticBridgeOutstanding
    empiricalAnchor : empiricalStatus ≡ empiricalCalibrationOutstanding

open import Agda.Builtin.Equality using (_≡_)
