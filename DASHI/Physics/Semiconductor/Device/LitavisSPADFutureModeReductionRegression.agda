module DASHI.Physics.Semiconductor.Device.LitavisSPADFutureModeReductionRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Semiconductor.Device.LitavisSPADFutureModeReductionExact as FutureMode

record LitavisFutureModeReductionRegression : Set where
  constructor litavis-future-mode-reduction-regression
  field
    sameCurrentSurfaceCanHideFutureDifference :
      FutureMode.FutureModeHistoryWitness
    currentSurfaceCandidateIsRefutedByFutureConsumer :
      FutureMode.FutureModeReductionFailure
    futureSafetyRemainsSeparateFromStaticCurrentAgreement :
      FutureMode.FutureModeBoundary

canonicalLitavisFutureModeReductionRegression :
  LitavisFutureModeReductionRegression
canonicalLitavisFutureModeReductionRegression =
  litavis-future-mode-reduction-regression
    FutureMode.canonicalFutureModeHistoryWitness
    FutureMode.canonicalFutureModeReductionFailure
    FutureMode.canonicalFutureModeBoundary
