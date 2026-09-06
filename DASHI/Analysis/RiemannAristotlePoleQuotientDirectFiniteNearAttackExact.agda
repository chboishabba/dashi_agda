module DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _+_; -_; _*_)

import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Literal

------------------------------------------------------------------------
-- DIRECT FINITE POLE-NEAR ATTACK
--
-- Final carrier to be evaluated:
--
--   sum_{sigma in nearOffFinset(t,J)}
--     4 m_sigma integral g_pole(u) cosh(a_sigma u)
--                         cos((b_sigma-t)u) du.
--
-- This owner does three things.
--
-- (1) It isolates the exact data a direct finite proof must retain.
-- (2) It proves, on a finite calibration carrier, that count/magnitude data do
--     not determine the signed total.
-- (3) BIDI strengthening: every future direct producer must name the existing
--     LiteralTargetCenteredScalarProblem it realizes, with literal Scalar and
--     ZeroIndex carrier identities plus explicit same-object obligations for the
--     target, near family, multiplicity, ordinate gap and signed total.
--
-- Therefore a DirectFinitePoleNearProducer is no longer allowed to be an
-- unrelated finite exponential sum that happens to have matching field names.
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

    -- Exact canonical G2 owner that this direct producer claims to realize.
    literalProblem : Literal.LiteralTargetCenteredScalarProblem

    scalarCarrierIdentity :
      Scalar ≡ Literal.LiteralTargetCenteredScalarProblem.Scalar literalProblem

    zeroIndexCarrierIdentity :
      ZeroIndex ≡ Literal.LiteralTargetCenteredScalarProblem.ZeroIndex literalProblem

    -- These semantic same-object witnesses remain proof obligations of the
    -- concrete application; they are not inferred from matching names.
    targetIsLiteralTarget : Set
    nearIndexIsLiteralNearOff : Set
    multiplicityIsLiteralMultiplicity : Set
    horizontalDisplacementIsLiteralOffRealPart : Set
    targetRelativeGapIsLiteralOrdinateMinusTarget : Set
    finiteSignedNearValueIsLiteralTotalSignedResponse : Set
    signedCosineCellIsLiteralKernelResponse : Set

    producerReference : String

open DirectFinitePoleNearProducer public

------------------------------------------------------------------------
-- Direct producer automatically exposes the literal target-centred gap shape.
------------------------------------------------------------------------

directProducerNamesLiteralProblem :
  (d : DirectFinitePoleNearProducer) → Literal.LiteralTargetCenteredScalarProblem
directProducerNamesLiteralProblem d = literalProblem d

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

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

    directProducerMustNameLiteralG2ScalarProblem : Bool
    directProducerMustNameLiteralG2ScalarProblemIsTrue :
      directProducerMustNameLiteralG2ScalarProblem ≡ true

    directProducerMayUseUnrelatedZeroCarrier : Bool
    directProducerMayUseUnrelatedZeroCarrierIsFalse :
      directProducerMayUseUnrelatedZeroCarrier ≡ false

    directFiniteEvaluationClosed : Bool
    directFiniteEvaluationClosedIsFalse : directFiniteEvaluationClosed ≡ false

    nextTheorem : String

canonicalDirectFiniteNearAttackBoundary : DirectFiniteNearAttackBoundary
canonicalDirectFiniteNearAttackBoundary =
  direct-finite-near-attack-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Instantiate DirectFinitePoleNearProducer on the existing literal G2 target-centred scalar problem: same Scalar/ZeroIndex, actual nearOff family, multiplicity, off-real displacement, ordinate-minus-target gap, literal signed kernel and totalSignedResponse. Supply an explicit approximant/error strong enough for the RH complement window. Do not construct another generic zero sum."
