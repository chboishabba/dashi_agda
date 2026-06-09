module DASHI.Physics.Closure.YMKillingBoundaryChildProofCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionLightweightBoundary
  as Opposite
import DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationLightweightBoundary
  as Flux
import DASHI.Physics.Closure.YMKillingBoundaryGaugeQuotientDescentLightweightBoundary
  as Descent
import DASHI.Physics.Closure.YMKillingBoundaryQuotientSymmetryLightweightBoundary
  as Symmetry

record YMKillingBoundaryChildProofCompositeLightweightBoundary : Set where
  field
    oppositeFaceBoundary :
      Opposite.YMKillingBoundaryOppositeFaceInvolutionLightweightBoundary
    oppositeFaceBoundaryIsCanonical :
      oppositeFaceBoundary
        ≡ Opposite.canonicalYMKillingBoundaryOppositeFaceInvolutionLightweightBoundary
    fluxCancellationBoundary :
      Flux.YMKillingBoundaryFluxCancellationLightweightBoundary
    fluxCancellationBoundaryIsCanonical :
      fluxCancellationBoundary
        ≡ Flux.canonicalYMKillingBoundaryFluxCancellationLightweightBoundary
    gaugeQuotientDescentBoundary :
      Descent.YMKillingBoundaryGaugeQuotientDescentLightweightBoundary
    gaugeQuotientDescentBoundaryIsCanonical :
      gaugeQuotientDescentBoundary
        ≡ Descent.canonicalYMKillingBoundaryGaugeQuotientDescentLightweightBoundary
    quotientSymmetryBoundary :
      Symmetry.YMKillingBoundaryQuotientSymmetryLightweightBoundary
    quotientSymmetryBoundaryIsCanonical :
      quotientSymmetryBoundary
        ≡ Symmetry.canonicalYMKillingBoundaryQuotientSymmetryLightweightBoundary
    childProofCompositeRecorded :
      Bool
    childProofCompositeRecordedIsTrue :
      childProofCompositeRecorded ≡ true
    ym1TheoremStillFalse :
      Opposite.YM1PromotedFromOppositeFace ≡ false
    fluxStillFalse :
      Flux.FluxCancellationTheoremProvedLightweight ≡ false
    descentStillFalse :
      Descent.GaugeQuotientDescentTheoremProvedLightweight ≡ false
    symmetryStillFalse :
      Symmetry.QuotientSymmetryTheoremProvedLightweight ≡ false

canonicalYMKillingBoundaryChildProofCompositeLightweightBoundary :
  YMKillingBoundaryChildProofCompositeLightweightBoundary
canonicalYMKillingBoundaryChildProofCompositeLightweightBoundary =
  record
    { oppositeFaceBoundary =
        Opposite.canonicalYMKillingBoundaryOppositeFaceInvolutionLightweightBoundary
    ; oppositeFaceBoundaryIsCanonical = refl
    ; fluxCancellationBoundary =
        Flux.canonicalYMKillingBoundaryFluxCancellationLightweightBoundary
    ; fluxCancellationBoundaryIsCanonical = refl
    ; gaugeQuotientDescentBoundary =
        Descent.canonicalYMKillingBoundaryGaugeQuotientDescentLightweightBoundary
    ; gaugeQuotientDescentBoundaryIsCanonical = refl
    ; quotientSymmetryBoundary =
        Symmetry.canonicalYMKillingBoundaryQuotientSymmetryLightweightBoundary
    ; quotientSymmetryBoundaryIsCanonical = refl
    ; childProofCompositeRecorded = true
    ; childProofCompositeRecordedIsTrue = refl
    ; ym1TheoremStillFalse = refl
    ; fluxStillFalse = refl
    ; descentStillFalse = refl
    ; symmetryStillFalse = refl
    }

