module DASHI.Core.InverseProblemIdentifiabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC INVERSE-PROBLEM / IDENTIFIABILITY BIDI CORE
--
-- Shared theorem-shape only.  Domain models remain separate.
------------------------------------------------------------------------

record ForwardModel : Set₁ where
  constructor forward-model
  field
    Latent Observable : Set
    forward : Latent → Observable
    modelReference : String

open ForwardModel public

record Calibration : Set₁ where
  constructor calibration
  field
    Raw Calibrated : Set
    calibrate : Raw → Calibrated
    calibrationReference : String

open Calibration public

record IdentifiabilityWitness (M : ForwardModel) : Set where
  constructor identifiability-witness
  field
    left right : Latent M
    sameObservable : forward M left ≡ forward M right

open IdentifiabilityWitness public

record GloballyIdentifiable (M : ForwardModel) : Set where
  constructor globally-identifiable
  field
    injectiveForward : (x y : Latent M) → forward M x ≡ forward M y → x ≡ y

open GloballyIdentifiable public

record MultiChannelModel : Set₁ where
  constructor multi-channel-model
  field
    Latent : Set
    O₁ O₂ : Set
    f₁ : Latent → O₁
    f₂ : Latent → O₂
    fusionReference : String

open MultiChannelModel public

record FusionSeparates (M : MultiChannelModel) : Set where
  constructor fusion-separates
  field
    separates : (x y : Latent M) →
      f₁ M x ≡ f₁ M y →
      f₂ M x ≡ f₂ M y →
      x ≡ y

open FusionSeparates public

record InverseProblemBoundary : Set where
  constructor inverse-problem-boundary
  field
    calibratedObservationIsLatentState : Bool
    calibratedObservationIsLatentStateIsFalse : calibratedObservationIsLatentState ≡ false
    oneChannelAutomaticallyIdentifiable : Bool
    oneChannelAutomaticallyIdentifiableIsFalse : oneChannelAutomaticallyIdentifiable ≡ false
    sameObservableAlwaysMeansSameLatent : Bool
    sameObservableAlwaysMeansSameLatentIsFalse : sameObservableAlwaysMeansSameLatent ≡ false
    addingIndependentChannelCanReduceDegeneracy : Bool
    addingIndependentChannelCanReduceDegeneracyIsTrue : addingIndependentChannelCanReduceDegeneracy ≡ true
    modelIdentifiabilityNeedsProof : Bool
    modelIdentifiabilityNeedsProofIsTrue : modelIdentifiabilityNeedsProof ≡ true

canonicalInverseProblemBoundary : InverseProblemBoundary
canonicalInverseProblemBoundary = inverse-problem-boundary
  false refl false refl false refl true refl true refl

record InverseProblemReverseObligation : Set where
  constructor inverse-problem-reverse-obligation
  field
    domain : String
    latentTarget : String
    observation : String
    missingCalibration : String
    missingForwardModel : String
    missingDegeneracyTest : String
    optionalSecondChannel : String

open InverseProblemReverseObligation public
