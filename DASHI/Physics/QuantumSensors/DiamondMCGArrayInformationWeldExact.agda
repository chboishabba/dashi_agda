module DASHI.Physics.QuantumSensors.DiamondMCGArrayInformationWeldExact where

------------------------------------------------------------------------
-- Diamond MCG / array information, phase P1 / W1.
--
-- Prior mathematics: Cauchy--Schwarz (nineteenth century); finite complex
-- carrier and exact finite support owner:
-- NSTriadKNExactFiniteComplexCauchySchwarzRound65.
-- Physical experiment: Omar et al. (2026), Science Advances eaeg5281.
--
-- ALL theorems here are conditional on explicitly supplied finite CS,
-- measured covariance-to-whitening identification and score calibration.
-- No physical noise model, sensor count or kilometres-range detection is
-- inferred from these abstract results.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNExactFiniteComplexCauchySchwarzRound65 as CS

-- Arbitrary finite list of channel indices: no restriction to 2, 10,
-- 100 or 1,000 elements, and no assumption of independent noise.
-- The actual inverse-covariance whitened response is an additional physical
-- calibration obligation, explicitly NOT manufactured by this theorem.
allNWhitenedInformationUpperBound :
  ∀ {i r} {Index : Set i} {F : C3.RealField r}
    (O : L2.OrderedRealExtension F)
    (support : List Index)
    (certificate : CS.ExactFiniteComplexCauchySchwarz O support)
    (whitenedFilter whitenedCardiacSignal : Index → C3.Complex F) →
    L2._≤_ O
      (CS.finiteComplexInnerProductModulusSquared
        support whitenedFilter whitenedCardiacSignal)
      (C3.multiply F
        (L2.finiteComplexL2NormSquared support whitenedFilter)
        (L2.finiteComplexL2NormSquared support whitenedCardiacSignal))
allNWhitenedInformationUpperBound O support certificate w signal =
  CS.finiteCauchySchwarz certificate w signal

-- Generic optimal value and an exact achieved detector, rather than an
-- unproved claim that a particular physical array has the optimum.
record AttainedOptimum {ℓ : Level} (Filter Value : Set ℓ)
    (_≤_ : Value → Value → Set ℓ) : Set (lsuc ℓ) where
  field
    score : Filter → Value
    chosen : Filter
    optimum : Value
    allBelow : ∀ filter → _≤_ (score filter) optimum
    chosenAttains : score chosen ≡ optimum
open AttainedOptimum public

-- This is the exact information-monotonicity weld for extending a sensing
-- array. 'extend' is the keep-old-channels/ignore-new-ones embedding. The
-- old detector's calibrated score must actually be preserved, and the
-- extended optimum must be attained; these are explicit assumptions.
-- No independence or sqrt(N) premise is used.
addedSensorsCannotReduceAttainableInformation :
  ∀ {ℓ} {Old New Value : Set ℓ}
    {_≤_ : Value → Value → Set ℓ}
    (old : AttainedOptimum Old Value _≤_)
    (new : AttainedOptimum New Value _≤_)
    (extend : Old → New)
    (preservesScore : ∀ detector →
      score new (extend detector) ≡ score old detector) →
    _≤_ (optimum old) (optimum new)
addedSensorsCannotReduceAttainableInformation old new extend preservesScore
  rewrite sym (chosenAttains old)
        | sym (preservesScore (chosen old)) =
  allBelow new (extend (chosen old))


-- General filtering loss control: a finite filter may reject noise AND
-- signal. The physical response to a projector needs an explicit receipt.
-- This record prevents any downstream inference that lower filtered noise
-- alone implies better detection.
record SignalPreservationReceipt {ℓ : Level}
    (Filter Signal Noise : Set ℓ) : Set (lsuc ℓ) where
  field
    filteredSignal : Filter → Signal → Signal
    filteredNoise : Filter → Noise → Noise
    signalScore : Signal → Noise → Signal
    originalSignal : Signal
    originalNoise : Noise
    chosenFilter : Filter
    filteredScore : Signal
    responseScoreIdentified :
      signalScore
        (filteredSignal chosenFilter originalSignal)
        (filteredNoise chosenFilter originalNoise)
      ≡ filteredScore
open SignalPreservationReceipt public

verifiedSignalScore :
  ∀ {ℓ} {Filter Signal Noise : Set ℓ}
    (receipt : SignalPreservationReceipt Filter Signal Noise) →
    signalScore receipt
      (filteredSignal receipt (chosenFilter receipt) (originalSignal receipt))
      (filteredNoise receipt (chosenFilter receipt) (originalNoise receipt))
      ≡ filteredScore receipt
verifiedSignalScore receipt = responseScoreIdentified receipt
