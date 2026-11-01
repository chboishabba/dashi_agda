module DASHI.Analysis.RiemannG21PoleMainModeSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- G21 terminology boundary.
--
-- Two different objects are easy to call "the pole/main mode":
--
-- 1. Literal Weil explicit-formula pole contribution
--      h(i/2) + h(-i/2),
--    which is a two-evaluation object before any further specialization.
--
-- 2. A prime-counting/PNT deterministic main mode obtained only after
--    unfolding the prime term through Chebyshev/partial-summation machinery,
--    schematically psi(t) = t + discrepancy(t).
--
-- They may be analytically related, but current DASHI does not identify them
-- definitionally and the existing PrimeCountingTransforms module keeps the
-- required transform/interchange theory as explicit obligations.
------------------------------------------------------------------------

data MainModeRole : Set where
  literalWeilPositivePoleEvaluation : MainModeRole
  literalWeilNegativePoleEvaluation : MainModeRole
  primeCountingDeterministicMain : MainModeRole
  primeCountingDiscrepancy : MainModeRole

record MainModeTransportBridge : Set₁ where
  field
    WeilPoleCarrier PrimeCountingCarrier : Set
    literalPositive literalNegative : WeilPoleCarrier
    deterministicPrimeMain : PrimeCountingCarrier
    discrepancyPrimePart : PrimeCountingCarrier

    TransformJustification : Set
    PoleToPrimeMainCompatibility : Set

    transformJustification : TransformJustification
    poleToPrimeMainCompatibility : PoleToPrimeMainCompatibility

    bridgeReading : String

record PoleMainModeBoundary : Set where
  constructor poleMainModeBoundary
  field
    literalWeilPoleHasTwoEvaluationRoles : Bool
    literalWeilPoleHasTwoEvaluationRolesIsTrue :
      literalWeilPoleHasTwoEvaluationRoles ≡ true

    pntMainModeDefinitionallyEqualsOneWeilPoleEvaluation : Bool
    pntMainModeDefinitionallyEqualsOneWeilPoleEvaluationIsFalse :
      pntMainModeDefinitionallyEqualsOneWeilPoleEvaluation ≡ false

    pntMainModeDefinitionallyEqualsSumOfTwoWeilPoleEvaluations : Bool
    pntMainModeDefinitionallyEqualsSumOfTwoWeilPoleEvaluationsIsFalse :
      pntMainModeDefinitionallyEqualsSumOfTwoWeilPoleEvaluations ≡ false

    transportBridgeCurrentlyDerived : Bool
    transportBridgeCurrentlyDerivedIsFalse :
      transportBridgeCurrentlyDerived ≡ false

canonicalPoleMainModeBoundary : PoleMainModeBoundary
canonicalPoleMainModeBoundary =
  poleMainModeBoundary
    true refl
    false refl
    false refl
    false refl
