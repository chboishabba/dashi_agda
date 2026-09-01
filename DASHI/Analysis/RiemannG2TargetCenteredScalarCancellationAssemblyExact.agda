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
-- infrastructure.  The RH payment is therefore not "have Fourier analysis" or
-- "have a vanishing-moment theorem".  It is a same-object receipt on the exact
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
-- Search pruning.  Structural facts about q only matter if they compile into
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
    false refl
    false refl
    false refl
    "Treat parity/Fourier/moment/integration-by-parts machinery as ordinary infrastructure. The only live G2d analytic payment is a same-object theorem on the literal determinant taper q and literal near-zero phase family that constructs TargetCenteredScalarCancellationReceipt. Any structural theorem on q is search-relevant only through that compiler; and even a successful scalar bound does not erase the separate projective-balance contradiction boundary."
