module DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as G2d
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e

------------------------------------------------------------------------
-- FINAL SCALAR BIDI ASSEMBLY
--
-- All generic harmonic-analysis machinery is treated as existing repository
-- infrastructure. The RH payment is therefore not "have Fourier analysis" or
-- "have a vanishing-moment theorem". It is a same-object receipt on the exact
-- q, near-zero family, multiplicities, zero parameters, target and cutoff that
-- feed the literal G2d/G2e consumer.
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
--
-- This is the exact ordinate coordinate already present inside dSigma:
--
--   delta_sigma = b_sigma - t.
--
-- Defining it here prevents the clustering lane from inventing another local
-- zero carrier. The second moment uses the SAME finiteNearSum operator and SAME
-- multiplicity function as the literal signed G2 response.
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

-- The literal kernel field already uses this exact gap; this theorem merely
-- exposes the named coordinate without changing the mathematical object.
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
    consumerReference : String

open TargetCenteredScalarCancellationReceipt public

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
    false refl
    false refl
    "The target-relative ordinate gap delta_sigma = ordinate(sigma)-target and its weighted finite-near second moment are now literal observables of the SAME G2 scalar problem: M2_delta = finiteNearSum (m_sigma * delta_sigma^2). Do not invent another moment carrier. Generic harmonic machinery remains infrastructure; the live analytic payment is a same-object quantitative theorem on this literal problem strong enough for the signed G2 consumer and/or clustering compiler. A scalar receipt still does not bypass the separate projective-balance boundary, and RH is not derived."
