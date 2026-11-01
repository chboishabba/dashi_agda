module DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact where

------------------------------------------------------------------------
-- WHOLE-SPACE R^3 REALIZATION OF THE DOMAIN-INDEPENDENT SIGNED CORE
--
-- This owner is intentionally NOT a T^3 -> R^3 transport theorem.
--
-- The frequency carrier is literal constructive R^3 over the repository's
-- Bishop real backend.  A continuous interaction is represented after
-- eliminating the convolution delta constraint:
--
--       xi , eta , zeta = xi - eta.
--
-- The physical Fourier/Gram layer supplies the actual scalar observables on
-- that interaction.  The only theorem required to inhabit
-- SignedFrequencyCarrier is the same exact pointwise centered-resolvent split
-- already isolated from periodic B.
--
-- This file therefore makes A a second REALIZATION of the common signed core:
--
--       periodic : Z^3 / counting
--       euclidean: R^3 / Lebesgue
--
-- It does not assert B => A, does not use a lattice limit, and does not claim
-- that the Lebesgue aggregation or low-frequency estimate is already paid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNSignedFrequencyCarrierExact as Core

record R3Frequency : Set where
  constructor r3-frequency
  field
    x y z : BishopReal.ℝ

open R3Frequency public

r3Add : R3Frequency → R3Frequency → R3Frequency
r3Add a b =
  r3-frequency
    (BishopReal._+_ (x a) (x b))
    (BishopReal._+_ (y a) (y b))
    (BishopReal._+_ (z a) (z b))

r3Negate : R3Frequency → R3Frequency
r3Negate a =
  r3-frequency
    (BishopReal.- (x a))
    (BishopReal.- (y a))
    (BishopReal.- (z a))

r3Subtract : R3Frequency → R3Frequency → R3Frequency
r3Subtract a b = r3Add a (r3Negate b)

record R3FrequencyEquivalent (a b : R3Frequency) : Set where
  constructor r3-frequency-equivalent
  field
    xEquivalent : BishopReal._≃_ (x a) (x b)
    yEquivalent : BishopReal._≃_ (y a) (y b)
    zEquivalent : BishopReal._≃_ (z a) (z b)

open R3FrequencyEquivalent public

record EuclideanInteraction : Set where
  constructor euclidean-interaction
  field
    xi eta : R3Frequency
    zeta : R3Frequency
    resonance : R3FrequencyEquivalent xi (r3Add eta zeta)

open EuclideanInteraction public

convolutionInteraction :
  (xi eta : R3Frequency) →
  R3FrequencyEquivalent xi
    (r3Add eta (r3Subtract xi eta)) →
  EuclideanInteraction
convolutionInteraction xi eta resonance =
  euclidean-interaction xi eta (r3Subtract xi eta) resonance

------------------------------------------------------------------------
-- Same-object physical scalar surface.
--
-- Bishop reals use setoid equality analytically, while SignedFrequencyCarrier
-- currently uses propositional equality for its scalar theorem.  The Fourier
-- realization therefore carries the exact checked equality produced by the
-- concrete physical owner.  This is not an assumed estimate: it is the
-- pointwise algebraic weld that the subsequent physical realization must
-- discharge.
------------------------------------------------------------------------

record EuclideanSignedFluxData : Set₁ where
  field
    weightedFluxR3 : EuclideanInteraction → BishopReal.ℝ
    commonResolventFluxR3 : EuclideanInteraction → BishopReal.ℝ
    centeredResolventCorrectionR3 : EuclideanInteraction → BishopReal.ℝ

    pointwiseCenteredResolventSplitR3 :
      (interaction : EuclideanInteraction) →
      weightedFluxR3 interaction
      ≡
      BishopReal._-_
        (commonResolventFluxR3 interaction)
        (centeredResolventCorrectionR3 interaction)

open EuclideanSignedFluxData public

euclideanSignedFrequencyCarrier :
  EuclideanSignedFluxData →
  Core.SignedFrequencyCarrier
euclideanSignedFrequencyCarrier dataSet = record
  { Core.Interaction = EuclideanInteraction
  ; Core.Scalar = BishopReal.ℝ
  ; Core._minus_ = BishopReal._-_
  ; Core.weightedFlux = weightedFluxR3 dataSet
  ; Core.commonResolventFlux = commonResolventFluxR3 dataSet
  ; Core.centeredResolventCorrection =
      centeredResolventCorrectionR3 dataSet
  ; Core.pointwiseCenteredResolventSplit =
      pointwiseCenteredResolventSplitR3 dataSet
  }

euclideanCarrierUsesLiteralR3Frequencies : Bool
euclideanCarrierUsesLiteralR3Frequencies = true

euclideanCarrierUsesContinuousConvolutionInteraction : Bool
euclideanCarrierUsesContinuousConvolutionInteraction = true

euclideanCarrierObtainedFromPeriodicTransport : Bool
euclideanCarrierObtainedFromPeriodicTransport = false

euclideanCarrierRequiresLatticeLimit : Bool
euclideanCarrierRequiresLatticeLimit = false

lebesgueAggregationClosedHere : Bool
lebesgueAggregationClosedHere = false

lowFrequencyCenteredCorrectionPaidHere : Bool
lowFrequencyCenteredCorrectionPaidHere = false

clayPromotion : Bool
clayPromotion = false

data PeriodicToEuclideanAutomaticTransport : Set where

periodicDoesNotAutomaticallyProduceEuclideanCarrier :
  PeriodicToEuclideanAutomaticTransport → ⊥
periodicDoesNotAutomaticallyProduceEuclideanCarrier ()

euclideanCarrierUsesLiteralR3FrequenciesIsTrue :
  euclideanCarrierUsesLiteralR3Frequencies ≡ true
euclideanCarrierUsesLiteralR3FrequenciesIsTrue = refl

euclideanCarrierObtainedFromPeriodicTransportIsFalse :
  euclideanCarrierObtainedFromPeriodicTransport ≡ false
euclideanCarrierObtainedFromPeriodicTransportIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
