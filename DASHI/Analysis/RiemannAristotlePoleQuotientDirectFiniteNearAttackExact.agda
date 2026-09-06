module DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _+_; -_; _*_)

import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Literal

------------------------------------------------------------------------
-- DIRECT FINITE POLE-NEAR ATTACK
--
-- Final carrier:
--
--   sum_{sigma in nearOffFinset(t,J)}
--     4 m_sigma integral g_pole(u) cosh(a_sigma u)
--                         cos((b_sigma-t)u) du.
--
-- BIDI rule: this is not a second zero-sum ontology. Every successful producer
-- names the canonical LiteralTargetCenteredScalarProblem it realizes. All
-- preservation / same-object propositions are proof-bearing receipts.
--
-- `signedCosineCell` is retained only as a compatibility field for historical
-- consumers. The theorem-bearing kernel is the stronger integrated
-- Literal.dSigma / Literal.totalSignedResponse. No live RH payment may depend on
-- separately proving a semantics for the three-argument helper.
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

    -- Compatibility-only helper. Literal.dSigma is the authoritative kernel.
    signedCosineCell : Taper → Scalar → Scalar → Scalar

    finiteSignedNearValue : Scalar
    approximant : Scalar
    error : Scalar
    Within : Scalar → Scalar → Scalar → Set

    preservesPoleTaper : Set
    preservesPoleTaperReceipt : preservesPoleTaper

    preservesTargetRelativeGap : Set
    preservesTargetRelativeGapReceipt : preservesTargetRelativeGap

    preservesMultiplicity : Set
    preservesMultiplicityReceipt : preservesMultiplicity

    preservesFiniteNearIndex : Set
    preservesFiniteNearIndexReceipt : preservesFiniteNearIndex

    preservesSignedCosinePhase : Set
    preservesSignedCosinePhaseReceipt : preservesSignedCosinePhase

    independentOfProjectiveBalance : Set
    independentOfProjectiveBalanceReceipt : independentOfProjectiveBalance

    evaluationReceipt : Within finiteSignedNearValue approximant error

    literalProblem : Literal.LiteralTargetCenteredScalarProblem

    scalarCarrierIdentity :
      Scalar ≡ Literal.LiteralTargetCenteredScalarProblem.Scalar literalProblem

    zeroIndexCarrierIdentity :
      ZeroIndex ≡ Literal.LiteralTargetCenteredScalarProblem.ZeroIndex literalProblem

    targetIsLiteralTarget : Set
    targetIsLiteralTargetReceipt : targetIsLiteralTarget

    nearIndexIsLiteralNearOff : Set
    nearIndexIsLiteralNearOffReceipt : nearIndexIsLiteralNearOff

    multiplicityIsLiteralMultiplicity : Set
    multiplicityIsLiteralMultiplicityReceipt : multiplicityIsLiteralMultiplicity

    horizontalDisplacementIsLiteralOffRealPart : Set
    horizontalDisplacementIsLiteralOffRealPartReceipt :
      horizontalDisplacementIsLiteralOffRealPart

    targetRelativeGapIsLiteralOrdinateMinusTarget : Set
    targetRelativeGapIsLiteralOrdinateMinusTargetReceipt :
      targetRelativeGapIsLiteralOrdinateMinusTarget

    finiteSignedNearValueIsLiteralTotalSignedResponse : Set
    finiteSignedNearValueIsLiteralTotalSignedResponseReceipt :
      finiteSignedNearValueIsLiteralTotalSignedResponse

    -- Compatibility firewall, not a theorem-bearing analytic obligation.
    signedCosineCellIsLiteralKernelResponse : Set
    signedCosineCellIsLiteralKernelResponseReceipt :
      signedCosineCellIsLiteralKernelResponse

    producerReference : String

open DirectFinitePoleNearProducer public

------------------------------------------------------------------------
-- CANONICAL COMPILER FROM THE EXISTING LITERAL G2 SCALAR PROBLEM
--
-- Scalar, ZeroIndex, target, nearIndex, multiplicity, horizontal displacement,
-- target-relative gap and finite signed value are fixed by construction.
--
-- The only theorem-bearing quantitative input is
--
--   Within (Literal.totalSignedResponse P) approximant error.
--
-- The pole taper/cutoff remain explicit because the selected-window weld must
-- identify them. `signedCosineCell` survives only for API compatibility and gets
-- no separate semantic research payment.
------------------------------------------------------------------------

record LiteralDirectFiniteInput
    (P : Literal.LiteralTargetCenteredScalarProblem) : Set₁ where
  field
    Taper : Set
    poleTaper : Taper
    cutoff : Literal.Scalar P

    compatibilitySignedCosineCell :
      Taper → Literal.Scalar P → Literal.Scalar P → Literal.Scalar P

    approximant : Literal.Scalar P
    error : Literal.Scalar P
    Within :
      Literal.Scalar P → Literal.Scalar P → Literal.Scalar P → Set

    evaluationReceipt :
      Within (Literal.totalSignedResponse P) approximant error

    poleTaperRealization : Set
    poleTaperRealizationReceipt : poleTaperRealization

    directRouteIndependentOfProjectiveBalance : Set
    directRouteIndependentOfProjectiveBalanceReceipt :
      directRouteIndependentOfProjectiveBalance

    producerReference : String

open LiteralDirectFiniteInput public

compileLiteralDirectFiniteProducer :
  (P : Literal.LiteralTargetCenteredScalarProblem) →
  LiteralDirectFiniteInput P →
  DirectFinitePoleNearProducer
compileLiteralDirectFiniteProducer P input =
  direct-finite-pole-near-producer
    (Literal.Scalar P)
    (Literal.ZeroIndex P)
    (LiteralDirectFiniteInput.Taper input)
    (LiteralDirectFiniteInput.poleTaper input)
    (Literal.target P)
    (LiteralDirectFiniteInput.cutoff input)
    (Literal.nearOff P)
    (Literal.multiplicity P)
    (Literal.offRealPart P)
    (Literal.targetRelativeGap P)
    (LiteralDirectFiniteInput.compatibilitySignedCosineCell input)
    (Literal.totalSignedResponse P)
    (LiteralDirectFiniteInput.approximant input)
    (LiteralDirectFiniteInput.error input)
    (LiteralDirectFiniteInput.Within input)
    (LiteralDirectFiniteInput.poleTaperRealization input)
    (LiteralDirectFiniteInput.poleTaperRealizationReceipt input)
    ((Literal.targetRelativeGap P) ≡ (Literal.targetRelativeGap P))
    refl
    ((Literal.multiplicity P) ≡ (Literal.multiplicity P))
    refl
    ((Literal.nearOff P) ≡ (Literal.nearOff P))
    refl
    ((Literal.targetRelativeGap P) ≡ (Literal.targetRelativeGap P))
    refl
    (LiteralDirectFiniteInput.directRouteIndependentOfProjectiveBalance input)
    (LiteralDirectFiniteInput.directRouteIndependentOfProjectiveBalanceReceipt input)
    (LiteralDirectFiniteInput.evaluationReceipt input)
    P
    refl
    refl
    ((Literal.target P) ≡ (Literal.target P))
    refl
    ((Literal.nearOff P) ≡ (Literal.nearOff P))
    refl
    ((Literal.multiplicity P) ≡ (Literal.multiplicity P))
    refl
    ((Literal.offRealPart P) ≡ (Literal.offRealPart P))
    refl
    ((Literal.targetRelativeGap P) ≡ (Literal.targetRelativeGap P))
    refl
    ((Literal.totalSignedResponse P) ≡ (Literal.totalSignedResponse P))
    refl
    ((Literal.totalSignedResponse P) ≡ (Literal.totalSignedResponse P))
    refl
    (LiteralDirectFiniteInput.producerReference input)

compiledDirectTargetIsLiteral :
  ∀ (P : Literal.LiteralTargetCenteredScalarProblem)
    (input : LiteralDirectFiniteInput P) →
  target (compileLiteralDirectFiniteProducer P input) ≡ Literal.target P
compiledDirectTargetIsLiteral P input = refl

compiledDirectNearIndexIsLiteral :
  ∀ (P : Literal.LiteralTargetCenteredScalarProblem)
    (input : LiteralDirectFiniteInput P) →
  nearIndex (compileLiteralDirectFiniteProducer P input) ≡ Literal.nearOff P
compiledDirectNearIndexIsLiteral P input = refl

compiledDirectMultiplicityIsLiteral :
  ∀ (P : Literal.LiteralTargetCenteredScalarProblem)
    (input : LiteralDirectFiniteInput P) →
  multiplicityOf (compileLiteralDirectFiniteProducer P input)
    ≡ Literal.multiplicity P
compiledDirectMultiplicityIsLiteral P input = refl

compiledDirectGapIsLiteral :
  ∀ (P : Literal.LiteralTargetCenteredScalarProblem)
    (input : LiteralDirectFiniteInput P) →
  targetRelativeGap (compileLiteralDirectFiniteProducer P input)
    ≡ Literal.targetRelativeGap P
compiledDirectGapIsLiteral P input = refl

compiledDirectSignedValueIsLiteral :
  ∀ (P : Literal.LiteralTargetCenteredScalarProblem)
    (input : LiteralDirectFiniteInput P) →
  finiteSignedNearValue (compileLiteralDirectFiniteProducer P input)
    ≡ Literal.totalSignedResponse P
compiledDirectSignedValueIsLiteral P input = refl

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

    directProducerPreservationFieldsAreProofBearing : Bool
    directProducerPreservationFieldsAreProofBearingIsTrue :
      directProducerPreservationFieldsAreProofBearing ≡ true

    canonicalLiteralFieldsCompileWithoutFreshProof : Bool
    canonicalLiteralFieldsCompileWithoutFreshProofIsTrue :
      canonicalLiteralFieldsCompileWithoutFreshProof ≡ true

    legacySignedCosineCellIsLiveResearchPayment : Bool
    legacySignedCosineCellIsLiveResearchPaymentIsFalse :
      legacySignedCosineCellIsLiveResearchPayment ≡ false

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
    true refl
    true refl
    false refl
    false refl
    false refl
    "Start from the existing LiteralTargetCenteredScalarProblem and use compileLiteralDirectFiniteProducer. Scalar/ZeroIndex, target, nearOff, multiplicity, off-real displacement, delta = ordinate-target and totalSignedResponse are compiler output. The legacy signedCosineCell helper is compatibility-only because Literal.dSigma already owns the integrated kernel. The live analytic payment is now the consumer-useful Within(totalSignedResponse, approximant, error) estimate on the exact G2 scalar object, plus selected pole-taper/cutoff identity downstream. RH remains open."
