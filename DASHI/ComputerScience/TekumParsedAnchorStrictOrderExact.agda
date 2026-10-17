module DASHI.ComputerScience.TekumParsedAnchorStrictOrderExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base as ℤ using (_<_)
import Data.Integer.Properties as ℤP
open import Data.Rational.Base as ℚ using (_<_)

import DASHI.ComputerScience.TekumMonotoneMagnitudeExact as Monotone
import DASHI.ComputerScience.TekumParsedAnchorBlockOrderExact as Block
import DASHI.ComputerScience.TekumParsedAnchorCodeExact as Code
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumParsedPayloadOrderExact as PayloadOrder
import DASHI.ComputerScience.TekumRegimeChainExact as Chain
import DASHI.ComputerScience.TekumRegimeExponentIntervalExact as Interval
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- ARBITRARY SUCCESSFULLY PARSED ANCHOR ORDER
--
-- This is the direct, non-chain version of positive Proposition 4.  The full
-- radix code first selects a regime block.  Inside one regime, the payload
-- radix code selects exponent first and fraction second.  Each structural
-- case then compiles through the existing exact rational monotonicity owners.
------------------------------------------------------------------------

earlierRegimeExponentStrict :
  ∀ {extra r s payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra s payload₂) →
  Chain.regimeIndex r < Chain.regimeIndex s →
  Interval.parsedExponentInteger left ℤ.< Interval.parsedExponentInteger right
earlierRegimeExponentStrict left right regimeLt =
  ℤP.≤-<-trans
    (Interval.parsedExponentUpper left)
    (ℤP.<-≤-trans
      (Chain.regimeIntervalsOrderedFromIndex regimeLt)
      (Interval.parsedExponentLower right))

parsedBlockOrderStrict :
  ∀ {extra r s payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra s payload₂) →
  Block.ParsedBlockOrder left right →
  Parsed.parsedMagnitude left ℚ.< Parsed.parsedMagnitude right
parsedBlockOrderStrict left right (Block.earlierRegime regimeLt) =
  Monotone.exponentStrictForcesMagnitudeStrict left right
    (earlierRegimeExponentStrict left right regimeLt)
parsedBlockOrderStrict {r = r} {s = s} left right
    (Block.sameRegimeSmallerPayload regimeEq payloadLt)
  with regimeEq
... | Agda.Builtin.Equality.refl =
  PayloadOrder.sameRegimePayloadOrderStrict left right
    (PayloadOrder.payloadCodeStrictImpliesSameRegimeOrder left right payloadLt)

parsedAnchorCodeStrictMagnitudeStrict :
  ∀ {extra r s payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra s payload₂) →
  Code.parsedAnchorCode left < Code.parsedAnchorCode right →
  Parsed.parsedMagnitude left ℚ.< Parsed.parsedMagnitude right
parsedAnchorCodeStrictMagnitudeStrict left right codeLt =
  parsedBlockOrderStrict left right
    (Block.parsedAnchorCodeStrictImpliesBlockOrder left right codeLt)
