module DASHI.ComputerScience.TekumParsedPayloadInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base using (cast; _++_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)

import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumParsedExponentInjectiveExact as ExponentInjective
import DASHI.ComputerScience.TekumParsedFieldRecoveryExact as Recovery
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSourceWordRoundTripExact as RoundTrip

------------------------------------------------------------------------
-- EXACT PARSER PAYLOAD RECOVERY
--
-- The numerical uniqueness layer recovers regime, exponent field and fraction
-- field.  This owner closes the dependent parser tail itself.  In particular,
-- the equality proof carried by ParsedPayload is proof-irrelevant; it cannot
-- hide a second source payload with the same recovered fields.
------------------------------------------------------------------------

sameRegimeFieldsDeterminePayload :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Source.exponentMSB p ≡ Source.exponentMSB q →
  Source.fractionMSB p ≡ Source.fractionMSB q →
  payload₁ ≡ payload₂
sameRegimeFieldsDeterminePayload p q exponentEq fractionEq =
  trans
    (Source.payloadJoin p)
    (trans castFieldsEq (sym (Source.payloadJoin q)))
  where
  lengthEq : Source.fieldLength p ≡ Source.fieldLength q
  lengthEq = ≡-irrelevant (Source.fieldLength p) (Source.fieldLength q)

  castFieldsEq :
    cast (Source.fieldLength p)
      (Source.exponentMSB p ++ Source.fractionMSB p)
    ≡
    cast (Source.fieldLength q)
      (Source.exponentMSB q ++ Source.fractionMSB q)
  castFieldsEq
    rewrite exponentEq | fractionEq | lengthEq = refl

-- This is the complete positive-magnitude parser injectivity statement: the
-- arbitrary-gap theorem identifies the exponent, the source table identifies
-- the regime, and the literal dependent payload is then reconstructed.
equalMagnitudeDeterminesRegimeAndPayload :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  (r ≡ s) × (payload₁ ≡ payload₂)
equalMagnitudeDeterminesRegimeAndPayload p q magnitudeEq
  with Recovery.equalMagnitudeForceRegime p q magnitudeEq
... | refl =
  refl , sameRegimeFieldsDeterminePayload p q exponentFieldEq fractionFieldEq
  where
  exponentIntegerEq =
    ExponentInjective.equalParsedMagnitudesForceExponent p q magnitudeEq

  exponentFieldEq =
    Recovery.equalExponentSameRegimeForceExponentMSB p q exponentIntegerEq

  fractionFieldEq =
    Recovery.equalMagnitudeSameRegimeForceFractionMSB p q magnitudeEq

-- Reattaching the source regime prefix therefore gives the same complete
-- parsed anchor word.  This is the exact handoff to the signed source-word
-- inverse; it does not appeal to cardinality.
equalMagnitudeDeterminesRejoinedAnchor :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  RoundTrip.rejoinAnchorMSB r payload₁
  ≡ RoundTrip.rejoinAnchorMSB s payload₂
equalMagnitudeDeterminesRejoinedAnchor {r = r} p q magnitudeEq
  with equalMagnitudeDeterminesRegimeAndPayload p q magnitudeEq
... | refl , payloadEq =
  cong (RoundTrip.rejoinAnchorMSB r) payloadEq
