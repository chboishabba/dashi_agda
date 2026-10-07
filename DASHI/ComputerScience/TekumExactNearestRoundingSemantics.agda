module DASHI.ComputerScience.TekumExactNearestRoundingSemantics where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Maybe.Base using (just)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _≤_; ∣_∣)
open import Data.Vec.Base using (Vec)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- DASHI EXACT-NEAREST ROUNDING SEMANTICS
--
-- This owner is intentionally independent of Hunhold Proposition 5.  The
-- source parser and exact rational decoder remain semantic authority; raw
-- anchor truncation does not occur in this file.
------------------------------------------------------------------------

record FiniteTekumWord (extra : Nat) : Set where
  constructor finiteTekumWord
  field
    word : Vec Trit.Trit (8 + extra)
    ordinary : Sem.OrdinaryTekum
    decoderSameObject :
      Source.parseTekumWord word ≡ just (Sem.ordinary ordinary)
open FiniteTekumWord public

finiteWordValue :
  ∀ {extra} → FiniteTekumWord extra → ℚ
finiteWordValue candidate = Exact.ordinaryRational (ordinary candidate)

tekumDistance : ℚ → ℚ → ℚ
tekumDistance x y = ∣ x - y ∣

finiteDistance :
  ∀ {sourceExtra targetExtra} →
  FiniteTekumWord sourceExtra →
  FiniteTekumWord targetExtra →
  ℚ
finiteDistance source target =
  tekumDistance (finiteWordValue source) (finiteWordValue target)

Nearest :
  ∀ {sourceExtra targetExtra} →
  FiniteTekumWord sourceExtra →
  FiniteTekumWord targetExtra →
  Set
Nearest {targetExtra = targetExtra} source chosen =
  (other : FiniteTekumWord targetExtra) →
  finiteDistance source chosen ≤ finiteDistance source other

record NearestSet
    {sourceExtra targetExtra : Nat}
    (source : FiniteTekumWord sourceExtra) : Set where
  constructor nearestSet
  field
    candidate : FiniteTekumWord targetExtra
    candidateIsNearest : Nearest source candidate
open NearestSet public

------------------------------------------------------------------------
-- Reserved NaR / special-zero / infinity strings cannot inhabit
-- FiniteTekumWord unless the existing source parser itself reports them as an
-- ordinary value, which it does not.  The exclusion is therefore by the
-- same-object decoder receipt, not by a second classifier in this semantics.
------------------------------------------------------------------------

record DASHIExactNearestSemanticBoundary : Set where
  constructor dashiExactNearestSemanticBoundary
  field
    sourceParserReused : Set
    exactRationalDecoderReused : Set
    specialsExcludedByOrdinaryDecoderReceipt : Set
    rawTruncationIsNotSemanticAuthority : Set
