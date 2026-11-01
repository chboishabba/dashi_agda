module DASHI.ComputerScience.TekumSourceOrderExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base as ℤ using (_<_)
open import Data.Rational.Base as ℚ using (_<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ
import DASHI.ComputerScience.TekumFractionSuccessorExact as FractionStep
import DASHI.ComputerScience.TekumMonotoneMagnitudeExact as Monotone
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumSignificandRangeExact as Sig
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- PROP. 4 THREE-CASE NUMERIC COMPILER
--
-- Hunhold's adjacent positive-code proof has exactly three cases after the
-- source anchor successor is split across fraction/exponent/regime fields.
-- This owner compiles those cases to strict rational magnitude order.  The
-- remaining structural leaf is only to extract one of these constructors from
-- an adjacent successfully parsed source pair.
------------------------------------------------------------------------

data PositiveAdjacentOrder
    {extra r s payload₁ payload₂}
    (p : Source.ParsedPayload extra r payload₁)
    (q : Source.ParsedPayload extra s payload₂) : Set where
  fractionStops :
    Succ.HasSuccessor (Source.fractionLST p) →
    Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q →
    Source.fractionLST q ≡ Succ.successorWord (Source.fractionLST p) →
    PositiveAdjacentOrder p q

  exponentStops :
    Factor.sourceExponentInteger p ℤ.< Factor.sourceExponentInteger q →
    PositiveAdjacentOrder p q

  regimeStops :
    Factor.sourceExponentInteger p ℤ.< Factor.sourceExponentInteger q →
    PositiveAdjacentOrder p q

fractionCarryStrict :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Succ.HasSuccessor (Source.fractionLST p) →
  Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q →
  Source.fractionLST q ≡ Succ.successorWord (Source.fractionLST p) →
  Parsed.parsedMagnitude p ℚ.< Parsed.parsedMagnitude q
fractionCarryStrict p q carry exponentEq fractionEq =
  Monotone.sameExponentSignificandStrictForcesMagnitudeStrict
    p q exponentEq significandLt
  where
  significandLt :
    Sig.significand (Source.fractionLST p)
    ℚ.< Sig.significand (Source.fractionLST q)
  significandLt =
    subst
      (λ f → Sig.significand (Source.fractionLST p) ℚ.< Sig.significand f)
      (sym fractionEq)
      (FractionStep.significandSuccessorStrict carry)

positiveAdjacentSourceCodeStrict :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  PositiveAdjacentOrder p q →
  Parsed.parsedMagnitude p ℚ.< Parsed.parsedMagnitude q
positiveAdjacentSourceCodeStrict p q (fractionStops carry exponentEq fractionEq) =
  fractionCarryStrict p q carry exponentEq fractionEq
positiveAdjacentSourceCodeStrict p q (exponentStops exponentLt) =
  Monotone.exponentStrictForcesMagnitudeStrict p q exponentLt
positiveAdjacentSourceCodeStrict p q (regimeStops exponentLt) =
  Monotone.exponentStrictForcesMagnitudeStrict p q exponentLt

-- Named source-facing endpoint for the already-extracted adjacent carry view.
-- It deliberately does not claim that extraction is paid here.
hunholdProposition4PositiveAdjacent :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  PositiveAdjacentOrder p q →
  Parsed.parsedMagnitude p ℚ.< Parsed.parsedMagnitude q
hunholdProposition4PositiveAdjacent = positiveAdjacentSourceCodeStrict
