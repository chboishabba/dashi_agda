module DASHI.ComputerScience.TekumSourceWordInjectiveExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (_+_)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumParsedPayloadInjectiveExact as Payload
import DASHI.ComputerScience.TekumParserSuccessfulRejoinExact as Parser
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSignedMagnitudeInjectiveExact as Signed
import DASHI.ComputerScience.TekumSourceAnchorInjectiveExact as SourceAnchor
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- HUNHOLD PROPOSITION 2: ORDINARY SOURCE-WORD INJECTIVITY
--
-- The theorem is stated on successful ordinary parser witnesses and explicit
-- nonzero external-sign witnesses.  The special zero/NaR/infinity encodings
-- remain owned by the separate source special-value classifier.
------------------------------------------------------------------------

ordinarySignedMagnitudeEquality :
  ∀ {extra r s payload₁ payload₂}
  (left right : Vec Trit.Trit (8 + extra))
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Source.ordinaryRationalFromParsed left p
    ≡ Source.ordinaryRationalFromParsed right q →
  DASHI.ComputerScience.TekumOrdinaryFactorizationExact.applyRationalSign
      (Source.signOfWord left) (Parsed.parsedMagnitude p)
    ≡
  DASHI.ComputerScience.TekumOrdinaryFactorizationExact.applyRationalSign
      (Source.signOfWord right) (Parsed.parsedMagnitude q)
ordinarySignedMagnitudeEquality left right p q valueEq =
  trans
    (sym (Parsed.parsedOrdinaryRationalIsSignedMagnitude left p))
    (trans valueEq
      (Parsed.parsedOrdinaryRationalIsSignedMagnitude right q))

ordinaryEqualDeterminesSign :
  ∀ {extra r s payload₁ payload₂}
  (left right : Vec Trit.Trit (8 + extra))
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Signed.OrdinarySign (Source.signOfWord left) →
  Signed.OrdinarySign (Source.signOfWord right) →
  Source.ordinaryRationalFromParsed left p
    ≡ Source.ordinaryRationalFromParsed right q →
  Source.signOfWord left ≡ Source.signOfWord right
ordinaryEqualDeterminesSign left right p q leftSign rightSign valueEq =
  proj₁
    (Signed.signedPositiveInjective
      leftSign rightSign
      (Parsed.parsedMagnitudePositive p)
      (Parsed.parsedMagnitudePositive q)
      (ordinarySignedMagnitudeEquality left right p q valueEq))

ordinaryEqualDeterminesMagnitude :
  ∀ {extra r s payload₁ payload₂}
  (left right : Vec Trit.Trit (8 + extra))
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Signed.OrdinarySign (Source.signOfWord left) →
  Signed.OrdinarySign (Source.signOfWord right) →
  Source.ordinaryRationalFromParsed left p
    ≡ Source.ordinaryRationalFromParsed right q →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q
ordinaryEqualDeterminesMagnitude left right p q leftSign rightSign valueEq =
  proj₂
    (Signed.signedPositiveInjective
      leftSign rightSign
      (Parsed.parsedMagnitudePositive p)
      (Parsed.parsedMagnitudePositive q)
      (ordinarySignedMagnitudeEquality left right p q valueEq))

ordinaryRationalInjectiveOnParsedWords :
  ∀ {extra r s payload₁ payload₂}
  (left right : Vec Trit.Trit (8 + extra))
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , p) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , q) →
  Signed.OrdinarySign (Source.signOfWord left) →
  Signed.OrdinarySign (Source.signOfWord right) →
  Source.ordinaryRationalFromParsed left p
    ≡ Source.ordinaryRationalFromParsed right q →
  left ≡ right
ordinaryRationalInjectiveOnParsedWords
    left right p q leftParse rightParse leftSign rightSign valueEq =
  SourceAnchor.sameSignAnchorDeterminesSourceWord signEq anchorEq
  where
  signEq : Source.signOfWord left ≡ Source.signOfWord right
  signEq =
    ordinaryEqualDeterminesSign left right p q leftSign rightSign valueEq

  magnitudeEq : Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q
  magnitudeEq =
    ordinaryEqualDeterminesMagnitude left right p q leftSign rightSign valueEq

  rejoinEq = Payload.equalMagnitudeDeterminesRejoinedAnchor p q magnitudeEq

  anchorEq =
    Parser.successfulParseDeterminesConcreteAnchor
      left right leftParse rightParse rejoinEq

-- Named paper-facing endpoint.  All arguments are literal source/parser
-- objects; there is no cardinality argument and no second rational semantics.
hunholdProposition2Injective :
  ∀ {extra r s payload₁ payload₂}
  (left right : Vec Trit.Trit (8 + extra))
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , p) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , q) →
  Signed.OrdinarySign (Source.signOfWord left) →
  Signed.OrdinarySign (Source.signOfWord right) →
  Source.ordinaryRationalFromParsed left p
    ≡ Source.ordinaryRationalFromParsed right q →
  left ≡ right
hunholdProposition2Injective = ordinaryRationalInjectiveOnParsedWords
