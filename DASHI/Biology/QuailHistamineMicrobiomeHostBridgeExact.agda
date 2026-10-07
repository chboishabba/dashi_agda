module DASHI.Biology.QuailHistamineMicrobiomeHostBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.QuailEggHistamineGutSnowballExact as Gut
import DASHI.Biology.Levin.MicrobiomeHostAppetiteBoundary as Host

record QuailHistamineMicrobiomeHostBridge : Set where
  constructor quail-histamine-microbiome-host-bridge
  field
    microbiomeHostBoundary : Host.MicrobiomeHostAppetiteBoundary
    microbialHistamineEvidence : Gut.IBSMicrobialHistamineReceipt
    histamineRoute : Host.AppetiteSignalRoute
    microbialMetaboliteRoutePresent : Bool
    microbialMetaboliteRoutePresentIsTrue : microbialMetaboliteRoutePresent ≡ true
    immuneRoutePresent : Bool
    immuneRoutePresentIsTrue : immuneRoutePresent ≡ true
    vagalOrNeuralRouteNotInferredFromHistamineStudy : Bool
    vagalOrNeuralRouteNotInferredFromHistamineStudyIsTrue :
      vagalOrNeuralRouteNotInferredFromHistamineStudy ≡ true
    appetiteOwnershipNotInferred : Bool
    appetiteOwnershipNotInferredIsTrue : appetiteOwnershipNotInferred ≡ true

canonicalHistamineRoute : Host.AppetiteSignalRoute
canonicalHistamineRoute = record
  { nutrientState = false
  ; gutMechanicalState = false
  ; enteroendocrineSignal = false
  ; vagalOrNeuralRoute = false
  ; immuneRoute = true
  ; microbialMetaboliteRoute = true
  ; learnedCueRoute = false
  ; hedonicRewardRoute = false
  ; routeInterventionsSpecified = true
  }

canonicalQuailHistamineMicrobiomeHostBridge : QuailHistamineMicrobiomeHostBridge
canonicalQuailHistamineMicrobiomeHostBridge = quail-histamine-microbiome-host-bridge
  Host.canonicalMicrobiomeHostAppetiteBoundary
  Gut.dePalma2022IBSHistamineReceipt
  canonicalHistamineRoute
  true refl true refl true refl true refl

record QuailHistamineMicrobiomeHostBoundary : Set where
  constructor quail-histamine-microbiome-host-boundary
  field
    microbiomeInfluenceRetained : Bool
    microbiomeInfluenceRetainedIsTrue : microbiomeInfluenceRetained ≡ true
    microbialHistamineIsOneRouteNotWholeHostState : Bool
    microbialHistamineIsOneRouteNotWholeHostStateIsTrue :
      microbialHistamineIsOneRouteNotWholeHostState ≡ true
    immuneAndMetaboliteRoutesCanBeWelded : Bool
    immuneAndMetaboliteRoutesCanBeWeldedIsTrue :
      immuneAndMetaboliteRoutesCanBeWelded ≡ true
    neuralRouteRequiresSeparateEvidence : Bool
    neuralRouteRequiresSeparateEvidenceIsTrue : neuralRouteRequiresSeparateEvidence ≡ true
    appetiteOrCravingClaimNotPromoted : Bool
    appetiteOrCravingClaimNotPromotedIsTrue : appetiteOrCravingClaimNotPromoted ≡ true

canonicalQuailHistamineMicrobiomeHostBoundary : QuailHistamineMicrobiomeHostBoundary
canonicalQuailHistamineMicrobiomeHostBoundary = quail-histamine-microbiome-host-boundary
  true refl true refl true refl true refl true refl
