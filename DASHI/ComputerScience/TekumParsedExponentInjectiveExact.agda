module DASHI.ComputerScience.TekumParsedExponentInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ; _<_)
import Data.Integer.Properties as ℤP
open import Data.Product using (_,_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.ComputerScience.TekumExponentBandExact as Band
import DASHI.ComputerScience.TekumIntegerSuccessorGapExact as Gap
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor

------------------------------------------------------------------------
-- EQUAL POSITIVE PARSED MAGNITUDES FORCE EQUAL INTEGER EXPONENTS
------------------------------------------------------------------------

leftExponentStrictContradiction :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Factor.sourceExponentInteger p < Factor.sourceExponentInteger q →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  ⊥
leftExponentStrictContradiction p q e<e' magnitudeEq
  with Gap.integerLessHasPositiveAdvance e<e'
... | k , stepEq =
  Band.positiveGapBandsDisjoint
    k
    (Parsed.parsedMagnitudeInExponentBand p)
    qBandAtGap
    magnitudeEq
  where
  qBandAtGap :
    Band.InBand
      (Band.advanceExponent (Agda.Builtin.Nat.suc k)
        (Factor.sourceExponentInteger p))
      (Parsed.parsedMagnitude q)
  qBandAtGap =
    subst
      (λ e → Band.InBand e (Parsed.parsedMagnitude q))
      (sym stepEq)
      (Parsed.parsedMagnitudeInExponentBand q)

rightExponentStrictContradiction :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Factor.sourceExponentInteger q < Factor.sourceExponentInteger p →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  ⊥
rightExponentStrictContradiction p q e'<e magnitudeEq =
  leftExponentStrictContradiction q p e'<e (sym magnitudeEq)

equalParsedMagnitudesForceExponent :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q
equalParsedMagnitudesForceExponent p q magnitudeEq
  with ℤP.<-cmp
    (Factor.sourceExponentInteger p)
    (Factor.sourceExponentInteger q)
... | tri< e<e' _ _ =
  ⊥-elim (leftExponentStrictContradiction p q e<e' magnitudeEq)
... | tri≈ _ exponentEq _ = exponentEq
... | tri> _ _ e'>e =
  ⊥-elim (rightExponentStrictContradiction p q e'>e magnitudeEq)
