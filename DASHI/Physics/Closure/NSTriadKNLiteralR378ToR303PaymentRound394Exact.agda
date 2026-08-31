module DASHI.Physics.Closure.NSTriadKNLiteralR378ToR303PaymentRound394Exact where

------------------------------------------------------------------------
-- ROUND394 / LITERAL R378 TEMPORAL REALIZATION -> THE ACTUAL R303 PAYMENT
--
-- R303's record is intentionally scalar and therefore cannot by itself say
-- what its `signedGramIntegral` denotes.  R393 fixes that semantic seam first:
-- its integral is literally the integral of the R378 global Gram-debt
-- observable, and its endpoints are literally the R290/R392 off-diagonal flux.
--
-- This adapter then imports the asymmetric endpoint payments of R302 and one
-- weighted-remainder bound.  The resulting R303 record has
--
--   signedGramIntegral = Integral literalGlobalGramDebt
--
-- definitionally.  Thus downstream R293/R353 no longer need an external
-- equality saying that the R303 scalar happens to be the R378 integral.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact as R393
import DASHI.Physics.Closure.NSTriadKNAsymmetricResolventEndpointRound302Exact as R302
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303

record LiteralR378PaymentLeaves
    {t : Level} {Time : Set t}
    (temporal : R393.LiteralR378TemporalRealization Time) : Set (lsuc t) where
  field
    endpoints : R302.AsymmetricResolventEndpointPayment

    initialEndpointSameObject :
      R302.initialOffDiagonal endpoints
      ≡ R393.literalOffDiagonalFlux temporal (R393.initialTime temporal)

    terminalEndpointSameObject :
      R302.terminalNegativeOffDiagonal endpoints
      ≡ 0ℚ - R393.literalOffDiagonalFlux temporal (R393.finalTime temporal)

    weightedRemainderUpper : ℚ
    weightedRemainderPaid :
      R393.Integral temporal (R393.literalWeightedRemainder temporal)
      ≤ weightedRemainderUpper

open LiteralR378PaymentLeaves public

literalR378ToR303Payment :
  ∀ {t} {Time : Set t}
    (temporal : R393.LiteralR378TemporalRealization Time) →
    LiteralR378PaymentLeaves temporal →
    R303.SignedGramFluxPayment
literalR378ToR303Payment temporal leaves = record
  { R303.signedGramIntegral =
      R393.Integral temporal (R393.literalGlobalGramDebt temporal)
  ; R303.initialFlux =
      R393.literalOffDiagonalFlux temporal (R393.initialTime temporal)
  ; R303.terminalNegativeFlux =
      0ℚ - R393.literalOffDiagonalFlux temporal (R393.finalTime temporal)
  ; R303.weightedRemainderIntegral =
      R393.Integral temporal (R393.literalWeightedRemainder temporal)
  ; R303.initialUpper = R302.initialDataUpperBound (endpoints leaves)
  ; R303.terminalUpper = R302.terminalDiagonalUpperBound (endpoints leaves)
  ; R303.remainderUpper = weightedRemainderUpper leaves
  ; R303.fluxIdentity = fluxIdentityExact
  ; R303.initialPaid = initialPaidExact
  ; R303.terminalPaid = terminalPaidExact
  ; R303.remainderPaid = weightedRemainderPaid leaves
  }
  where
  integrated = R393.literalR378IntegratedGramFluxIdentity temporal

  fluxIdentityExact :
    R393.Integral temporal (R393.literalGlobalGramDebt temporal)
    ≡
    R393.literalOffDiagonalFlux temporal (R393.initialTime temporal)
    + (0ℚ - R393.literalOffDiagonalFlux temporal (R393.finalTime temporal))
    + R393.Integral temporal (R393.literalWeightedRemainder temporal)
  fluxIdentityExact =
    trans integrated
      (solve
        ( R393.literalOffDiagonalFlux temporal (R393.initialTime temporal)
        ∷ R393.literalOffDiagonalFlux temporal (R393.finalTime temporal)
        ∷ R393.Integral temporal (R393.literalWeightedRemainder temporal)
        ∷ []))

  initialPaidExact :
    R393.literalOffDiagonalFlux temporal (R393.initialTime temporal)
    ≤ R302.initialDataUpperBound (endpoints leaves)
  initialPaidExact =
    subst
      (λ x → x ≤ R302.initialDataUpperBound (endpoints leaves))
      (initialEndpointSameObject leaves)
      (R302.initialFluxPaidByData (endpoints leaves))

  terminalPaidExact :
    (0ℚ - R393.literalOffDiagonalFlux temporal (R393.finalTime temporal))
    ≤ R302.terminalDiagonalUpperBound (endpoints leaves)
  terminalPaidExact =
    subst
      (λ x → x ≤ R302.terminalDiagonalUpperBound (endpoints leaves))
      (terminalEndpointSameObject leaves)
      (R302.terminalFluxPaidByPositiveCompletion (endpoints leaves))

literalR378SignedIntegralIsDefinitionallyR303Integral :
  ∀ {t} {Time : Set t}
    (temporal : R393.LiteralR378TemporalRealization Time)
    (leaves : LiteralR378PaymentLeaves temporal) →
  R303.signedGramIntegral (literalR378ToR303Payment temporal leaves)
  ≡ R393.Integral temporal (R393.literalGlobalGramDebt temporal)
literalR378SignedIntegralIsDefinitionallyR303Integral temporal leaves = refl

round394R303SameObjectIntegralSeamClosedModuloTemporalLeaves : Bool
round394R303SameObjectIntegralSeamClosedModuloTemporalLeaves = true

round394R303ScalarChosenIndependently : Bool
round394R303ScalarChosenIndependently = false

round394ActualFTCProducerRecovered : Bool
round394ActualFTCProducerRecovered = false

round394R303SameObjectIntegralSeamClosedModuloTemporalLeavesIsTrue :
  round394R303SameObjectIntegralSeamClosedModuloTemporalLeaves ≡ true
round394R303SameObjectIntegralSeamClosedModuloTemporalLeavesIsTrue = refl
