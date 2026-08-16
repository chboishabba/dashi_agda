module DASHI.Foundations.ContextualCounterpositionNotDoubleInversionExact where

------------------------------------------------------------------------
-- CONTEXTUAL COUNTERPOSITION IS NOT DOUBLE INVERSION
--
-- This closes the remaining operator-algebra seam without overloading the
-- informal glyph `is(x) != !!x` with an untyped meaning.
--
-- Existing repository semantics already distinguish:
--   * strict inversion of all three balanced-ternary coordinates; and
--   * context-indexed counterposition, which may reject only one coordinate.
--
-- Double strict inversion returns the original triad.  A partial contextual
-- counterposition need not.  The theorem below makes that distinction exact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.CounterpositionOrderedJoinExact as Counter

invertDigitInvolutive :
  (digit : BT.BalancedDigit) →
  BT.invertDigit (BT.invertDigit digit) ≡ digit
invertDigitInvolutive BT.neg = refl
invertDigitInvolutive BT.zeroDigit = refl
invertDigitInvolutive BT.pos = refl

strictInverseInvolutive :
  (pattern : BT.TriadPattern) →
  BT.strictInverse (BT.strictInverse pattern) ≡ pattern
strictInverseInvolutive (BT.triad first second third)
  rewrite invertDigitInvolutive first
        | invertDigitInvolutive second
        | invertDigitInvolutive third = refl

------------------------------------------------------------------------
-- Concrete separating witness.
--
-- For (+++):
--   reject-third counterposition = (++-)
--   double strict inversion      = (+++).
------------------------------------------------------------------------

rejectThirdAllPositiveNotDoubleInverse :
  Counter.counterUnder Counter.rejectThird BT.allPositive
  ≡ BT.strictInverse (BT.strictInverse BT.allPositive)
  → ⊥
rejectThirdAllPositiveNotDoubleInverse ()

record OperatorSeparationWitness : Set where
  constructor operatorSeparationWitness
  field
    input : BT.TriadPattern
    contextualOutput : BT.TriadPattern
    doubleInverseOutput : BT.TriadPattern
    contextualExact :
      Counter.counterUnder Counter.rejectThird input ≡ contextualOutput
    doubleInverseExact :
      BT.strictInverse (BT.strictInverse input) ≡ doubleInverseOutput
    outputsDistinct : contextualOutput ≡ doubleInverseOutput → ⊥

canonicalOperatorSeparationWitness : OperatorSeparationWitness
canonicalOperatorSeparationWitness =
  operatorSeparationWitness
    BT.allPositive
    BT.thirdCoordinateCounterposition
    BT.allPositive
    refl
    (strictInverseInvolutive BT.allPositive)
    (λ ())

------------------------------------------------------------------------
-- Generic boundary: the result concerns these typed operators only.  Any
-- external `is`, negation, reversal, dialectical or linguistic operator must
-- provide an explicit bridge before inheriting this theorem.
------------------------------------------------------------------------

record ContextualCounterpositionBoundary : Set where
  constructor contextualCounterpositionBoundary
  field
    strictDoubleInverseReturnsInput : Bool
    contextualCounterpositionAlwaysReturnsInput : Bool
    contextualCounterpositionEqualsDoubleInverse : Bool
    untypedIsOperatorAutomaticallyIdentified : Bool

canonicalContextualCounterpositionBoundary : ContextualCounterpositionBoundary
canonicalContextualCounterpositionBoundary =
  contextualCounterpositionBoundary true false false false
