module DASHI.Physics.Closure.NSTriadKNEuclideanSignedGramPairCarrierRealizationExact where

------------------------------------------------------------------------
-- A / CANONICAL CONTINUOUS SAME-OUTPUT PAIR CARRIER
--
-- The periodic R290 object is indexed by an ordered pair of interactions with
-- one common output.  A single Euclidean convolution cell is therefore too
-- small a carrier for the literal continuous analogue.
--
-- Eliminate both convolution delta constraints at once:
--
--   alpha = (xi, eta_alpha, xi - eta_alpha)
--   beta  = (xi, eta_beta , xi - eta_beta).
--
-- The resulting interaction space is literally parameterised by
--
--   (xi, eta_alpha, eta_beta) in R^3 x R^3 x R^3,
--
-- with a shared output by construction.  This is the carrier on which the
-- off-diagonal projected Gram and centered-resolvent split must be integrated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNSignedFrequencyCarrierExact as Core
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean

canonicalConvolutionResonance :
  (output eta : Euclidean.R3Frequency) →
  Euclidean.R3FrequencyEquivalent
    output
    (Euclidean.r3Add eta (Euclidean.r3Subtract output eta))
canonicalConvolutionResonance output eta =
  let open BishopP.ℝ-Solver
  in
  Euclidean.r3-frequency-equivalent
    (solve 2
      (λ x e → x ⊜ e ⊕ (x ⊖ e))
      BishopP.≃-refl
      (Euclidean.x output) (Euclidean.x eta))
    (solve 2
      (λ x e → x ⊜ e ⊕ (x ⊖ e))
      BishopP.≃-refl
      (Euclidean.y output) (Euclidean.y eta))
    (solve 2
      (λ x e → x ⊜ e ⊕ (x ⊖ e))
      BishopP.≃-refl
      (Euclidean.z output) (Euclidean.z eta))

canonicalConvolutionInteraction :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  Euclidean.EuclideanInteraction
canonicalConvolutionInteraction output eta =
  Euclidean.convolutionInteraction
    output eta
    (canonicalConvolutionResonance output eta)

record EuclideanGramPairInteraction : Set where
  constructor euclidean-gram-pair-interaction
  field
    output : Euclidean.R3Frequency
    alphaEta betaEta : Euclidean.R3Frequency

open EuclideanGramPairInteraction public

alphaInteraction :
  EuclideanGramPairInteraction →
  Euclidean.EuclideanInteraction
alphaInteraction pair =
  canonicalConvolutionInteraction
    (output pair)
    (alphaEta pair)

betaInteraction :
  EuclideanGramPairInteraction →
  Euclidean.EuclideanInteraction
betaInteraction pair =
  canonicalConvolutionInteraction
    (output pair)
    (betaEta pair)

alphaOutputIsShared :
  (pair : EuclideanGramPairInteraction) →
  Euclidean.xi (alphaInteraction pair) ≡ output pair
alphaOutputIsShared pair = refl

betaOutputIsShared :
  (pair : EuclideanGramPairInteraction) →
  Euclidean.xi (betaInteraction pair) ≡ output pair
betaOutputIsShared pair = refl

record EuclideanSignedGramPairFluxData : Set₁ where
  field
    weightedFluxPair :
      EuclideanGramPairInteraction → BishopReal.ℝ

    commonResolventFluxPair :
      EuclideanGramPairInteraction → BishopReal.ℝ

    centeredResolventCorrectionPair :
      EuclideanGramPairInteraction → BishopReal.ℝ

    pointwiseCenteredResolventSplitPair :
      (pair : EuclideanGramPairInteraction) →
      weightedFluxPair pair
      ≡
      BishopReal._-_
        (commonResolventFluxPair pair)
        (centeredResolventCorrectionPair pair)

open EuclideanSignedGramPairFluxData public

euclideanSignedGramPairCarrier :
  EuclideanSignedGramPairFluxData →
  Core.SignedFrequencyCarrier
euclideanSignedGramPairCarrier dataSet = record
  { Core.Interaction = EuclideanGramPairInteraction
  ; Core.Scalar = BishopReal.ℝ
  ; Core._minus_ = BishopReal._-_
  ; Core.weightedFlux = weightedFluxPair dataSet
  ; Core.commonResolventFlux = commonResolventFluxPair dataSet
  ; Core.centeredResolventCorrection =
      centeredResolventCorrectionPair dataSet
  ; Core.pointwiseCenteredResolventSplit =
      pointwiseCenteredResolventSplitPair dataSet
  }

pairCarrierHasSharedOutputDefinitionally : Bool
pairCarrierHasSharedOutputDefinitionally = true

pairCarrierCoordinatesAreXiEtaAlphaEtaBeta : Bool
pairCarrierCoordinatesAreXiEtaAlphaEtaBeta = true

singleCellCarrierIsCanonicalR290Analogue : Bool
singleCellCarrierIsCanonicalR290Analogue = false

pairCarrierObtainedFromPeriodicLimit : Bool
pairCarrierObtainedFromPeriodicLimit = false

clayPromotion : Bool
clayPromotion = false

pairCarrierHasSharedOutputDefinitionallyIsTrue :
  pairCarrierHasSharedOutputDefinitionally ≡ true
pairCarrierHasSharedOutputDefinitionallyIsTrue = refl

singleCellCarrierIsCanonicalR290AnalogueIsFalse :
  singleCellCarrierIsCanonicalR290Analogue ≡ false
singleCellCarrierIsCanonicalR290AnalogueIsFalse = refl

pairCarrierObtainedFromPeriodicLimitIsFalse :
  pairCarrierObtainedFromPeriodicLimit ≡ false
pairCarrierObtainedFromPeriodicLimitIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
