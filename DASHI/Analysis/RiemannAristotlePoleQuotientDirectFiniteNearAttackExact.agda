module DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _+_; -_; _*_)

------------------------------------------------------------------------
-- DIRECT FINITE POLE-NEAR ATTACK
--
-- Final carrier to be evaluated:
--
--   sum_{sigma in nearOffFinset(t,J)}
--     4 m_sigma integral g_pole(u) cosh(a_sigma u)
--                         cos((b_sigma-t)u) du.
--
-- This owner does two things.
--
-- (1) It isolates the exact data a direct finite proof must retain.
-- (2) It proves, on a finite calibration carrier, that count/magnitude data do
--     not determine the signed total.  Therefore local-zero count or an
--     absolute cell envelope cannot by themselves close the consumer.
------------------------------------------------------------------------

record DirectFiniteNearCell : Set where
  constructor direct-finite-near-cell
  field
    multiplicity : ℚ
    absoluteEnvelope : ℚ
    signedPhaseResponse : ℚ

open DirectFiniteNearCell public

cellContribution : DirectFiniteNearCell → ℚ
cellContribution c = multiplicity c * signedPhaseResponse c

record DirectFiniteNearObservation : Set where
  constructor direct-finite-near-observation
  field
    countCode : ℚ
    envelopeCode : ℚ

sameCoarseObservation : DirectFiniteNearCell → DirectFiniteNearCell → Set
sameCoarseObservation x y =
  (multiplicity x ≡ multiplicity y) ×
  (absoluteEnvelope x ≡ absoluteEnvelope y)

positivePhaseCell : DirectFiniteNearCell
positivePhaseCell = direct-finite-near-cell (+ 1 / 1) (+ 1 / 1) (+ 1 / 1)

negativePhaseCell : DirectFiniteNearCell
negativePhaseCell = direct-finite-near-cell (+ 1 / 1) (+ 1 / 1) (- (+ 1 / 1))

sameCountAndEnvelope : sameCoarseObservation positivePhaseCell negativePhaseCell
sameCountAndEnvelope = refl , refl

positiveContribution : cellContribution positivePhaseCell ≡ (+ 1 / 1)
positiveContribution = refl

negativeContribution : cellContribution negativePhaseCell ≡ (- (+ 1 / 1))
negativeContribution = refl

------------------------------------------------------------------------
-- Literal direct-route receipt.
------------------------------------------------------------------------

record DirectFinitePoleNearProducer : Set₁ where
  constructor direct-finite-pole-near-producer
  field
    Scalar ZeroIndex Taper : Set
    poleTaper : Taper
    target : Scalar
    cutoff : Scalar

    nearIndex : ZeroIndex → Set
    multiplicityOf : ZeroIndex → Scalar
    horizontalDisplacement : ZeroIndex → Scalar
    targetRelativeGap : ZeroIndex → Scalar
    signedCosineCell : Taper → Scalar → Scalar → Scalar

    finiteSignedNearValue : Scalar
    approximant : Scalar
    error : Scalar
    Within : Scalar → Scalar → Scalar → Set

    preservesPoleTaper : Set
    preservesTargetRelativeGap : Set
    preservesMultiplicity : Set
    preservesFiniteNearIndex : Set
    preservesSignedCosinePhase : Set
    independentOfProjectiveBalance : Set

    evaluationReceipt : Within finiteSignedNearValue approximant error
    producerReference : String

open DirectFinitePoleNearProducer public

record DirectFiniteNearAttackBoundary : Set where
  constructor direct-finite-near-attack-boundary
  field
    localCountAloneDeterminesSignedNearValue : Bool
    localCountAloneDeterminesSignedNearValueIsFalse :
      localCountAloneDeterminesSignedNearValue ≡ false

    absoluteEnvelopeAloneDeterminesSignedNearValue : Bool
    absoluteEnvelopeAloneDeterminesSignedNearValueIsFalse :
      absoluteEnvelopeAloneDeterminesSignedNearValue ≡ false

    phaseSensitiveInformationRequired : Bool
    phaseSensitiveInformationRequiredIsTrue :
      phaseSensitiveInformationRequired ≡ true

    directFiniteEvaluationClosed : Bool
    directFiniteEvaluationClosedIsFalse : directFiniteEvaluationClosed ≡ false

    nextTheorem : String

canonicalDirectFiniteNearAttackBoundary : DirectFiniteNearAttackBoundary
canonicalDirectFiniteNearAttackBoundary =
  direct-finite-near-attack-boundary
    false refl
    false refl
    true refl
    false refl
    "Prove a phase-sensitive finite evaluation of the literal reflection-paired pole-near sum on nearOffFinset(t,J), preserving multiplicity and target-relative gaps, with an explicit approximant/error small enough for the RH complement window."
