module DASHI.Reasoning.MultiObserverScienceQuotientQualiaBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Biology.ObserverPerceptualManifoldResidual
  using
    ( ObserverPerceptualManifoldResidual
    ; SharedLatentTransportManifold
    ; crossSpeciesProjectionDefectRetained
    ; crossSpeciesProjectionDefectRetainedIsTrue
    ; observerProjectionPromoted
    ; observerProjectionPromotedIsTrue
    ; phenomenalInhabitationRecovered
    ; phenomenalInhabitationRecoveredIsFalse
    )

------------------------------------------------------------------------
-- Lemma 5: science as multi-observer quotient fusion.
--
-- The bridge promotes only quotient-level partial reconstruction across
-- observer channels.  It keeps the projection defect explicit and blocks
-- both latent-manifold recovery and inhabited-experience recovery.

data ObserverChannel : Set where
  humanScienceChannel :
    ObserverChannel

  birdScienceChannel :
    ObserverChannel

  batScienceChannel :
    ObserverChannel

  octopusScienceChannel :
    ObserverChannel

  beeScienceChannel :
    ObserverChannel

data Nonempty {A : Set} : List A → Set where
  nonempty-cons :
    (head : A) →
    (tail : List A) →
    Nonempty (head ∷ tail)

canonicalObserverChannels : List ObserverChannel
canonicalObserverChannels =
  humanScienceChannel
  ∷ birdScienceChannel
  ∷ batScienceChannel
  ∷ octopusScienceChannel
  ∷ beeScienceChannel
  ∷ []

canonicalObserverChannelsNonempty :
  Nonempty canonicalObserverChannels
canonicalObserverChannelsNonempty =
  nonempty-cons humanScienceChannel
    (birdScienceChannel
     ∷ batScienceChannel
     ∷ octopusScienceChannel
     ∷ beeScienceChannel
     ∷ [])

record MultiObserverQuotientFusion
    (manifold : SharedLatentTransportManifold) : Set₁ where
  field
    observerResidual :
      ObserverPerceptualManifoldResidual manifold

    observerChannels :
      List ObserverChannel

    observerChannelsNonempty :
      Nonempty observerChannels

    partialReconstructionPromoted :
      Bool

    partialReconstructionPromotedIsTrue :
      partialReconstructionPromoted ≡ true

    partialReconstructionFollowsObserverProjection :
      observerProjectionPromoted observerResidual
      ≡ partialReconstructionPromoted

    projectionDefectBounded :
      Bool

    projectionDefectBoundedIsTrue :
      projectionDefectBounded ≡ true

    projectionDefectBoundedByResidual :
      crossSpeciesProjectionDefectRetained observerResidual
      ≡ projectionDefectBounded

    latentManifoldRecovered :
      Bool

    latentManifoldRecoveredIsFalse :
      latentManifoldRecovered ≡ false

    inhabitedExperienceRecovered :
      Bool

    inhabitedExperienceRecoveredIsFalse :
      inhabitedExperienceRecovered ≡ false

    inhabitedExperienceRecoveryFollowsResidualBoundary :
      phenomenalInhabitationRecovered observerResidual
      ≡ inhabitedExperienceRecovered

    fusionReading :
      String

open MultiObserverQuotientFusion public

canonicalMultiObserverQuotientFusion :
  {manifold : SharedLatentTransportManifold} →
  (observerResidual :
    ObserverPerceptualManifoldResidual manifold) →
  MultiObserverQuotientFusion manifold
canonicalMultiObserverQuotientFusion observerResidual =
  record
    { observerResidual =
        observerResidual
    ; observerChannels =
        canonicalObserverChannels
    ; observerChannelsNonempty =
        canonicalObserverChannelsNonempty
    ; partialReconstructionPromoted =
        true
    ; partialReconstructionPromotedIsTrue =
        refl
    ; partialReconstructionFollowsObserverProjection =
        observerProjectionPromotedIsTrue observerResidual
    ; projectionDefectBounded =
        true
    ; projectionDefectBoundedIsTrue =
        refl
    ; projectionDefectBoundedByResidual =
        crossSpeciesProjectionDefectRetainedIsTrue observerResidual
    ; latentManifoldRecovered =
        false
    ; latentManifoldRecoveredIsFalse =
        refl
    ; inhabitedExperienceRecovered =
        false
    ; inhabitedExperienceRecoveredIsFalse =
        refl
    ; inhabitedExperienceRecoveryFollowsResidualBoundary =
        phenomenalInhabitationRecoveredIsFalse observerResidual
    ; fusionReading =
        "Lemma 5 records science as nonempty multi-observer quotient fusion: partial reconstruction and bounded projection defect are promoted, while latent manifold recovery and inhabited experience recovery stay fail-closed."
    }
