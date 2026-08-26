module DASHI.Cognition.PNF.StratifiedFibrewiseSupportLocalityRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Cognition.PNF.StratifiedFibrewiseSupportLocalityExact


data Stratum : Set where
  sentenceStratum : Stratum

data Fibre : Set where
  sentenceFibre : Fibre

data GlobalState : Set where
  smallAccumulation largeAccumulation : GlobalState

data Support : Set where
  sameLocalSupport : Support

data CloseResult : Set where
  locallyClosed : CloseResult

data WorkReceipt : Set where
  boundedLocalWork : WorkReceipt

supportProjectionExample : Stratum → Fibre → GlobalState → Support
supportProjectionExample _ _ _ = sameLocalSupport

closeSupportExample : Stratum → Fibre → Support → CloseResult
closeSupportExample _ _ _ = locallyClosed

workSupportExample : Stratum → Fibre → Support → WorkReceipt
workSupportExample _ _ _ = boundedLocalWork

closeGlobalExample : Fibre → GlobalState → CloseResult
closeGlobalExample _ _ = locallyClosed

workGlobalExample : Fibre → GlobalState → WorkReceipt
workGlobalExample _ _ = boundedLocalWork

exampleSystem :
  StratifiedFibrewiseSupportLocality
    Stratum Fibre GlobalState Support CloseResult WorkReceipt
exampleSystem = record
  { activeStratum = λ _ → sentenceStratum
  ; supportProjection = supportProjectionExample
  ; closeFromSupport = closeSupportExample
  ; workFromSupport = workSupportExample
  ; closeFromGlobal = closeGlobalExample
  ; workFromGlobal = workGlobalExample
  ; closeFactorsThroughSupport = λ _ _ → refl
  ; workFactorsThroughSupport = λ _ _ → refl
  }

-- The accumulated state can be different while the closing fibre exposes the
-- same support at its active sentence stratum.
localSupportIgnoresUnrelatedAccumulation :
  supportProjection exampleSystem sentenceStratum sentenceFibre smallAccumulation
    ≡ supportProjection exampleSystem sentenceStratum sentenceFibre largeAccumulation
localSupportIgnoresUnrelatedAccumulation = refl

closeIgnoresUnrelatedAccumulation :
  closeFromGlobal exampleSystem sentenceFibre smallAccumulation
    ≡ closeFromGlobal exampleSystem sentenceFibre largeAccumulation
closeIgnoresUnrelatedAccumulation =
  sameSupportSameClose
    exampleSystem
    sentenceFibre
    smallAccumulation
    largeAccumulation
    localSupportIgnoresUnrelatedAccumulation

workIgnoresUnrelatedAccumulation :
  workFromGlobal exampleSystem sentenceFibre smallAccumulation
    ≡ workFromGlobal exampleSystem sentenceFibre largeAccumulation
workIgnoresUnrelatedAccumulation =
  sameSupportSameWork
    exampleSystem
    sentenceFibre
    smallAccumulation
    largeAccumulation
    localSupportIgnoresUnrelatedAccumulation

data Extension : GlobalState → GlobalState → Set where
  addUnrelatedState : Extension smallAccumulation largeAccumulation

exampleAccumulationCertificate :
  SupportPreservingAccumulation exampleSystem Extension
exampleAccumulationCertificate = record
  { accumulationPreservesSupport = λ _ _ _ _ → refl
  }

certifiedExtensionKeepsCloseExact :
  closeFromGlobal exampleSystem sentenceFibre smallAccumulation
    ≡ closeFromGlobal exampleSystem sentenceFibre largeAccumulation
certifiedExtensionKeepsCloseExact =
  unrelatedAccumulationCannotChangeClose
    exampleAccumulationCertificate
    sentenceFibre
    smallAccumulation
    largeAccumulation
    addUnrelatedState

certifiedExtensionCannotIncreaseWork :
  workFromGlobal exampleSystem sentenceFibre smallAccumulation
    ≡ workFromGlobal exampleSystem sentenceFibre largeAccumulation
certifiedExtensionCannotIncreaseWork =
  unrelatedAccumulationCannotIncreaseWork
    exampleAccumulationCertificate
    sentenceFibre
    smallAccumulation
    largeAccumulation
    addUnrelatedState

data Residual : Set where
  localDelta : Residual

data Promoted : Set where
  promotedDelta : Promoted

examplePromotion :
  ProgressiveStratumPromotion Stratum Fibre Support Residual Promoted
examplePromotion = record
  { residualFromSupport = λ _ _ _ → localDelta
  ; promoteResidual = λ _ _ → promotedDelta
  }

sameSupportEmitsSameProgressiveResidual :
  residualFromSupport examplePromotion sentenceStratum sentenceFibre sameLocalSupport
    ≡ residualFromSupport examplePromotion sentenceStratum sentenceFibre sameLocalSupport
sameSupportEmitsSameProgressiveResidual =
  sameSupportSameResidual
    examplePromotion
    sentenceStratum
    sentenceFibre
    sameLocalSupport
    sameLocalSupport
    refl
