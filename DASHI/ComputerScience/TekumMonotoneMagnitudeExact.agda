module DASHI.ComputerScience.TekumMonotoneMagnitudeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base as ℤ using (_<_)
open import Data.Rational.Base as ℚ using (_<_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.ComputerScience.TekumExponentBandExact as Band
import DASHI.ComputerScience.TekumIntegerSuccessorGapExact as Gap
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumSignificandRangeExact as Sig
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale

------------------------------------------------------------------------
-- NUMERIC HALF OF HUNHOLD PROPOSITION 4
--
-- Once the source carry analysis says either
--   (a) the decoded exponent strictly increases, or
--   (b) the exponent is unchanged and the significand strictly increases,
-- the rational magnitude order is already forced.  This isolates the only
-- remaining Prop. 4 debt to the source integer-code successor/carry bridge.
------------------------------------------------------------------------

exponentStrictForcesMagnitudeStrict :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Factor.sourceExponentInteger p ℤ.< Factor.sourceExponentInteger q →
  Parsed.parsedMagnitude p < Parsed.parsedMagnitude q
exponentStrictForcesMagnitudeStrict p q exponentLt
  with Gap.integerLessHasPositiveAdvance exponentLt
... | k , advanceEq =
  Band.bandsOrderedByPositiveGap k
    (Parsed.parsedMagnitudeInExponentBand p)
    (subst
      (λ e → Band.InBand e (Parsed.parsedMagnitude q))
      (sym advanceEq)
      (Parsed.parsedMagnitudeInExponentBand q))

sameExponentSignificandStrictForcesMagnitudeStrict :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q →
  Sig.significand (Source.fractionLST p)
    < Sig.significand (Source.fractionLST q) →
  Parsed.parsedMagnitude p < Parsed.parsedMagnitude q
sameExponentSignificandStrictForcesMagnitudeStrict p q exponentEq significandLt
  rewrite Parsed.parsedMagnitudeIsSourceFormula p
        | Parsed.parsedMagnitudeIsSourceFormula q
        | exponentEq =
  let
    scale = Scale.triadicScale (Factor.sourceExponentInteger q)
    instance scalePositive : Positive scale
        scalePositive = positive (Scale.triadicScalePositive (Factor.sourceExponentInteger q))
  in
  ℚP.*-monoʳ-<-pos scale significandLt
