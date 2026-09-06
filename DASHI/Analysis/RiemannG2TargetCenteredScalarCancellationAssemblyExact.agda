module DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as G2d
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e

------------------------------------------------------------------------
-- FINAL SCALAR BIDI ASSEMBLY
--
-- All generic harmonic-analysis machinery is existing repository infrastructure.
-- The live theorem is on the exact q, near-zero family, multiplicities, zero
-- parameters and target used by the literal G2d/G2e consumer.
------------------------------------------------------------------------

record LiteralTargetCenteredScalarProblem : Set₁ where
  field
    Scalar Parameter ZeroIndex : Set

    zeroS fourS : Scalar
    addS subS mulS : Scalar -> Scalar -> Scalar
    coshS cosS : Scalar -> Scalar

    q : Parameter -> Scalar
    multiplicity : ZeroIndex -> Scalar
    offRealPart : ZeroIndex -> Scalar
    ordinate : ZeroIndex -> Scalar
    target : Scalar

    nearOff : ZeroIndex -> Set

    integrate : (Parameter -> Scalar) -> Scalar
    finiteNearSum : (ZeroIndex -> Scalar) -> Scalar

    dSigma : ZeroIndex -> Scalar
    totalSignedResponse : Scalar
    targetCenteredIntegral : Scalar

    dSigmaIsLiteralKernel :
      (sigma : ZeroIndex) ->
      dSigma sigma
      ≡ integrate
          (λ u ->
            mulS
              (mulS
                (mulS fourS (q u))
                (mulS
                  (multiplicity sigma)
                  (coshS (mulS (offRealPart sigma) u))))
              (cosS
                (mulS
                  (subS (ordinate sigma) target)
                  u)))

    totalSignedResponseIsFiniteNearSum :
      totalSignedResponse ≡ finiteNearSum dSigma

    totalSignedResponseIsTargetCenteredIntegral :
      totalSignedResponse ≡ targetCenteredIntegral

    exactQIsG2DeterminantTaper : Set
    exactNearFamilyIsG2NearOffFamily : Set
    exactZeroParametersAreLiteralSpectralZeros : Set
    exactTargetAndCutoffAreG2ConsumerParameters : Set

    AcceptableForG2Consumer : Scalar -> Set

open LiteralTargetCenteredScalarProblem public

------------------------------------------------------------------------
-- CANONICAL TARGET-GAP / SECOND-MOMENT OBSERVABLE
------------------------------------------------------------------------

targetRelativeGap :
  (P : LiteralTargetCenteredScalarProblem) -> ZeroIndex P -> Scalar P
targetRelativeGap P sigma = subS P (ordinate P sigma) (target P)

targetRelativeGapSq :
  (P : LiteralTargetCenteredScalarProblem) -> ZeroIndex P -> Scalar P
targetRelativeGapSq P sigma =
  mulS P (targetRelativeGap P sigma) (targetRelativeGap P sigma)

weightedTargetRelativeGapSq :
  (P : LiteralTargetCenteredScalarProblem) -> ZeroIndex P -> Scalar P
weightedTargetRelativeGapSq P sigma =
  mulS P (multiplicity P sigma) (targetRelativeGapSq P sigma)

targetRelativeGapSecondMoment :
  (P : LiteralTargetCenteredScalarProblem) -> Scalar P
targetRelativeGapSecondMoment P =
  finiteNearSum P (weightedTargetRelativeGapSq P)

dSigmaIsLiteralKernelViaTargetGap :
  (P : LiteralTargetCenteredScalarProblem) ->
  (sigma : ZeroIndex P) ->
  dSigma P sigma
  ≡ integrate P
      (λ u ->
        mulS P
          (mulS P
            (mulS P (fourS P) (q P u))
            (mulS P
              (multiplicity P sigma)
              (coshS P (mulS P (offRealPart P sigma) u))))
          (cosS P
            (mulS P
              (targetRelativeGap P sigma)
              u)))
dSigmaIsLiteralKernelViaTargetGap P sigma = dSigmaIsLiteralKernel P sigma

------------------------------------------------------------------------
-- Cancellation consumer.
------------------------------------------------------------------------

data ScalarCancellationMechanism : Set where
  targetCenteredPhasePairing
  exactFourierWindow
  vanishingMomentTransfer
  integrationByPartsDecay
  directSignedCosineEstimate
  : ScalarCancellationMechanism

record TargetCenteredScalarCancellationReceipt
    (P : LiteralTargetCenteredScalarProblem) : Set₁ where
  field
    mechanism : ScalarCancellationMechanism
    targetIntegralAccepted :
      AcceptableForG2Consumer P (targetCenteredIntegral P)

    sameLiteralProblemUsed : Set
    sameLiteralProblemUsedReceipt : sameLiteralProblemUsed

    consumerReference : String

open TargetCenteredScalarCancellationReceipt public

------------------------------------------------------------------------
-- Exact direct endpoint: acceptance of the literal total signed response is
-- already acceptance of the target-centred integral, because the canonical
-- problem owns their equality.
------------------------------------------------------------------------

subst : ∀ {A : Set} (Pred : A → Set) {x y : A} → x ≡ y → Pred x → Pred y
subst Pred refl px = px

record DirectSignedConsumerPayment
    (P : LiteralTargetCenteredScalarProblem) : Set₁ where
  field
    totalSignedResponseAccepted :
      AcceptableForG2Consumer P (totalSignedResponse P)
    paymentReference : String

open DirectSignedConsumerPayment public

directSignedPaymentClosesCancellationReceipt :
  (P : LiteralTargetCenteredScalarProblem) →
  DirectSignedConsumerPayment P →
  TargetCenteredScalarCancellationReceipt P
directSignedPaymentClosesCancellationReceipt P payment =
  record
    { mechanism = directSignedCosineEstimate
    ; targetIntegralAccepted =
        subst
          (AcceptableForG2Consumer P)
          (totalSignedResponseIsTargetCenteredIntegral P)
          (totalSignedResponseAccepted payment)
    ; sameLiteralProblemUsed = P ≡ P
    ; sameLiteralProblemUsedReceipt = refl
    ; consumerReference = paymentReference payment
    }

record ExistingTargetCenteredHarmonicMachinery
    (P : LiteralTargetCenteredScalarProblem) : Set₁ where
  field
    selectedMechanism : ScalarCancellationMechanism
    exactConsumerReceipt : TargetCenteredScalarCancellationReceipt P

open ExistingTargetCenteredHarmonicMachinery public

record G2dScalarConsumerClosure
    (P : LiteralTargetCenteredScalarProblem) : Set₁ where
  constructor g2d-scalar-consumer-closure
  field
    cancellationReceipt : TargetCenteredScalarCancellationReceipt P

existingMachineryClosesScalarConsumer :
  (P : LiteralTargetCenteredScalarProblem) ->
  ExistingTargetCenteredHarmonicMachinery P ->
  G2dScalarConsumerClosure P
existingMachineryClosesScalarConsumer P M =
  g2d-scalar-consumer-closure (exactConsumerReceipt M)

directSignedPaymentClosesScalarConsumer :
  (P : LiteralTargetCenteredScalarProblem) →
  DirectSignedConsumerPayment P →
  G2dScalarConsumerClosure P
directSignedPaymentClosesScalarConsumer P payment =
  g2d-scalar-consumer-closure
    (directSignedPaymentClosesCancellationReceipt P payment)

------------------------------------------------------------------------
-- Search pruning. Structural facts about q only matter if they compile into
-- the exact consumer receipt above.
------------------------------------------------------------------------

data QStructuralFact : Set where
  qEven
  qOdd
  qHasVanishingMoments
  qHasCompactFourierSupport
  qHasSignedFactorization
  qHasTargetPhaseIdentity
  : QStructuralFact

record QStructureCompiler
    (P : LiteralTargetCenteredScalarProblem)
    (fact : QStructuralFact) : Set₁ where
  field
    structuralReceipt : Set
    structuralReceiptWitness : structuralReceipt
    compilesToExactCancellation : TargetCenteredScalarCancellationReceipt P

open QStructureCompiler public

qStructureWithoutConsumerCompilationIsNotClosure : Bool
qStructureWithoutConsumerCompilationIsNotClosure = true

currentG2dStatusStillOpen :
  G2d.signedScalarDeterminantSumBoundClosed
    G2d.canonicalG2dScalarDeterminantSumTarget ≡ false
currentG2dStatusStillOpen =
  G2d.signedScalarDeterminantSumBoundClosedIsFalse
    G2d.canonicalG2dScalarDeterminantSumTarget

currentG2eStatusStillOpen :
  G2e.targetCenteredLocalZeroExponentialSumBoundClosed
    G2e.canonicalG2eDeterminantTaperKernelBoundary ≡ false
currentG2eStatusStillOpen =
  G2e.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    G2e.canonicalG2eDeterminantTaperKernelBoundary

record TargetCenteredScalarCancellationBoundary : Set where
  constructor target-centered-scalar-cancellation-boundary
  field
    genericHarmonicMachineryNeedsRebuildingInRH : Bool
    genericHarmonicMachineryNeedsRebuildingInRHIsFalse :
      genericHarmonicMachineryNeedsRebuildingInRH ≡ false

    literalTargetGapSecondMomentDefinedOnConsumerCarrier : Bool
    literalTargetGapSecondMomentDefinedOnConsumerCarrierIsTrue :
      literalTargetGapSecondMomentDefinedOnConsumerCarrier ≡ true

    directSignedAcceptanceCompilesToExactConsumerReceipt : Bool
    directSignedAcceptanceCompilesToExactConsumerReceiptIsTrue :
      directSignedAcceptanceCompilesToExactConsumerReceipt ≡ true

    genericWithinReceiptAloneClosesConsumer : Bool
    genericWithinReceiptAloneClosesConsumerIsFalse :
      genericWithinReceiptAloneClosesConsumer ≡ false

    exactSameObjectScalarReceiptIsTheLivePayment : Bool
    exactSameObjectScalarReceiptIsTheLivePaymentIsTrue :
      exactSameObjectScalarReceiptIsTheLivePayment ≡ true

    parityOrFourierLabelWithoutConsumerCompilationClosesG2d : Bool
    parityOrFourierLabelWithoutConsumerCompilationClosesG2dIsFalse :
      parityOrFourierLabelWithoutConsumerCompilationClosesG2d ≡ false

    projectiveBalanceBypassedByScalarReceipt : Bool
    projectiveBalanceBypassedByScalarReceiptIsFalse :
      projectiveBalanceBypassedByScalarReceipt ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalTargetCenteredScalarCancellationBoundary :
  TargetCenteredScalarCancellationBoundary
canonicalTargetCenteredScalarCancellationBoundary =
  target-centered-scalar-cancellation-boundary
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    "The exact target gap delta_sigma and M2_delta are literal observables of the SAME G2 scalar problem. A generic approximant/error relation is not itself closure. The direct theorem-bearing endpoint is now explicit: prove AcceptableForG2Consumer(totalSignedResponse) on this literal object. The canonical equality totalSignedResponse = targetCenteredIntegral then compiles that payment into TargetCenteredScalarCancellationReceipt and G2dScalarConsumerClosure. Moment/cosine/Fourier machinery is relevant only if it proves this exact payment or the independent clustering consumer. Projective balance and RH remain separate."
