module DASHI.Physics.Semiconductor.Device.LitavisSPADFutureModeReductionExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerRelativeReductionKernelExact as Kernel
import DASHI.Physics.Semiconductor.Device.LitavisSPADConsumerSafeReductionExact as Reduction

------------------------------------------------------------------------
-- LITAVIS SPAD FUTURE-MODE REDUCTION
--
-- Static agreement on the currently exposed sensor surface is not by itself a
-- future-safety certificate for a software-configurable sensing system.
-- Existing ConsumerRelativeReductionKernelExact already owns the relevant
-- history-sensitive future witness and candidate-refutation machinery.
--
-- This finite fixture is repository-local.  The Litavis source motivates the
-- software-configurable/multimodal question; it does not assert that these four
-- states or this action are a transistor-level model of Litavis.
------------------------------------------------------------------------

data ModeState : Set where
  dormantA dormantB activeA activeB : ModeState

data ModeAction : Set where
  revealTimingMode : ModeAction

data ModeSurface : Set where
  sameDormantSurface activeSurfaceA activeSurfaceB : ModeSurface

modeStep : ModeAction → ModeState → ModeState
modeStep revealTimingMode dormantA = activeA
modeStep revealTimingMode dormantB = activeB
modeStep revealTimingMode activeA = activeA
modeStep revealTimingMode activeB = activeB

modeSurface : ModeState → ModeSurface
modeSurface dormantA = sameDormantSurface
modeSurface dormantB = sameDormantSurface
modeSurface activeA = activeSurfaceA
modeSurface activeB = activeSurfaceB

FutureModeHistoryWitness : Set
FutureModeHistoryWitness =
  Kernel.HistorySensitiveFutureWitness modeStep modeSurface

canonicalFutureModeHistoryWitness : FutureModeHistoryWitness
canonicalFutureModeHistoryWitness =
  Kernel.historySensitiveFutureWitness
    dormantA
    dormantB
    refl
    revealTimingMode
    (λ ())

------------------------------------------------------------------------
-- The current-surface code is a candidate compression.  It collapses dormant
-- states now, but the declared future action exposes distinct observations.
-- The one-action trace therefore refutes universal safety of that candidate for
-- this future consumer language.
------------------------------------------------------------------------

currentSurfaceCode : ModeState → ModeSurface
currentSurfaceCode = modeSurface

FutureModeReductionFailure : Set
FutureModeReductionFailure =
  Kernel.CandidateReductionFailure
    modeStep
    modeSurface
    currentSurfaceCode

canonicalFutureModeReductionFailure : FutureModeReductionFailure
canonicalFutureModeReductionFailure =
  Kernel.candidateReductionFailure
    dormantA
    dormantB
    refl
    (revealTimingMode ∷ [])
    (λ ())

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FutureModeBoundary : Set where
  constructor future-mode-boundary
  field
    sameCurrentObservationImpliesSameFutureLanguage : Bool
    sameCurrentObservationImpliesSameFutureLanguageIsFalse :
      sameCurrentObservationImpliesSameFutureLanguage ≡ false
    softwareConfigurabilityRequiresFutureConsumerCheck : Bool
    softwareConfigurabilityRequiresFutureConsumerCheckIsTrue :
      softwareConfigurabilityRequiresFutureConsumerCheck ≡ true
    currentConsumerAdequacyIsFutureSafetyCertificate : Bool
    currentConsumerAdequacyIsFutureSafetyCertificateIsFalse :
      currentConsumerAdequacyIsFutureSafetyCertificate ≡ false
    oneSeparatingFutureTraceCanRefuteCandidateReduction : Bool
    oneSeparatingFutureTraceCanRefuteCandidateReductionIsTrue :
      oneSeparatingFutureTraceCanRefuteCandidateReduction ≡ true
    sourceClaimCreatesDynamicSafetyProof : Bool
    sourceClaimCreatesDynamicSafetyProofIsFalse :
      sourceClaimCreatesDynamicSafetyProof ≡ false
    reductionSourceAtlasRetained : Bool
    reductionSourceAtlasRetainedIsTrue : reductionSourceAtlasRetained ≡ true

canonicalFutureModeBoundary : FutureModeBoundary
canonicalFutureModeBoundary =
  future-mode-boundary
    false refl
    true refl
    false refl
    true refl
    false refl
    true refl

-- Keep the source snowball linked without promoting it into the proof above.
linkedReductionSourceAtlas : Reduction.ReductionSourceBoundary
linkedReductionSourceAtlas = Reduction.canonicalReductionSourceBoundary
