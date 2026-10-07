module DASHI.ComputerScience.TekumProposition4NegativeGlobalExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Data.Integer.Base as ℤ using (-[1+_])
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (_<_; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using (-_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedAnchorCodeExact as Code
import DASHI.ComputerScience.TekumParsedAnchorStrictOrderExact as Strict
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumProposition4PositiveGlobalExact as Positive
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as Center
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- GLOBAL NEGATIVE BRANCH OF HUNHOLD PROPOSITION 4
--
-- Negative source order reverses absolute magnitude.  Definition-7 anchors
-- are invariant under digitwise negation, so the positive rank theorem gives
-- the same exact anchor coordinate for a negative word's absolute magnitude.
-- Strict magnitude order is then reflected by rational negation.
------------------------------------------------------------------------

signOfNegativeWord :
  ∀ {n m} (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ -[1+ m ] →
  Source.signOfWord word ≡ Anchor.negativeSign
signOfNegativeWord word valueEq
  rewrite valueEq = refl

negativeParsedRationalIsNegMagnitude :
  ∀ {extra r payload m}
  (word : Vec Trit.Trit (8 Agda.Builtin.Nat.+ extra))
  (parsed : Source.ParsedPayload extra r payload) →
  BT.toInteger (BT.eval word) ≡ -[1+ m ] →
  Source.ordinaryRationalFromParsed word parsed
  ≡ ℚ.- (Parsed.parsedMagnitude parsed)
negativeParsedRationalIsNegMagnitude word parsed valueEq =
  trans
    (Parsed.parsedOrdinaryRationalIsSignedMagnitude word parsed)
    (cong
      (λ sign → Factor.applyRationalSign sign (Parsed.parsedMagnitude parsed))
      (signOfNegativeWord word valueEq))

negatedNegativeIsPositive :
  ∀ {n m} (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ -[1+ m ] →
  BT.toInteger (BT.eval (Fixed.negateWord word)) ≡ Data.Integer.Base.+ (suc m)
negatedNegativeIsPositive word valueEq
  rewrite Fixed.negateWordIsInvertWord word
        | BT.toIntegerInvertWord word
        | valueEq = refl

negativeAnchorNatCode :
  ∀ {n m}
  (even : Width.EvenWidth n)
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ -[1+ m ] →
  Positional.natCode (Fixed.concreteAnchor word)
  ≡ suc m + Center.sourceCenterMagnitudeAt even
negativeAnchorNatCode even word valueEq =
  trans
    (cong Positional.natCode
      (sym (Fixed.concreteAnchorNegationInvariant word)))
    (Positive.positiveAnchorNatCode
      even (Fixed.negateWord word)
      (negatedNegativeIsPositive word valueEq))

negativeSourceOrderReversesAnchorCode :
  ∀ {n m k}
  (even : Width.EvenWidth n)
  (left right : Vec Trit.Trit n) →
  BT.toInteger (BT.eval left) ≡ -[1+ m ] →
  BT.toInteger (BT.eval right) ≡ -[1+ k ] →
  k < m →
  Positional.natCode (Fixed.concreteAnchor right)
  < Positional.natCode (Fixed.concreteAnchor left)
negativeSourceOrderReversesAnchorCode {m = m} {k = k}
    even left right leftNegative rightNegative k<m
  rewrite negativeAnchorNatCode even right rightNegative
        | negativeAnchorNatCode even left leftNegative =
  NatP.+-monoʳ-<
    (Center.sourceCenterMagnitudeAt even)
    (s≤s k<m)

negativeParsedCodeReverseStrict :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂ m k}
  (even : Width.EvenWidth (8 Agda.Builtin.Nat.+ extra))
  (left right : Vec Trit.Trit (8 Agda.Builtin.Nat.+ extra)) →
  BT.toInteger (BT.eval left) ≡ -[1+ m ] →
  BT.toInteger (BT.eval right) ≡ -[1+ k ] →
  k < m →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Code.parsedAnchorCode parsed₂ < Code.parsedAnchorCode parsed₁
negativeParsedCodeReverseStrict even left right leftNegative rightNegative k<m
    leftParse rightParse
  rewrite sym (Code.successfulParseNatCode right rightParse)
        | sym (Code.successfulParseNatCode left leftParse) =
  negativeSourceOrderReversesAnchorCode
    even left right leftNegative rightNegative k<m

hunholdProposition4NegativeGlobal :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂ m k}
  (even : Width.EvenWidth (8 Agda.Builtin.Nat.+ extra))
  (left right : Vec Trit.Trit (8 Agda.Builtin.Nat.+ extra)) →
  BT.toInteger (BT.eval left) ≡ -[1+ m ] →
  BT.toInteger (BT.eval right) ≡ -[1+ k ] →
  k < m →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Source.ordinaryRationalFromParsed left parsed₁
    ℚ.< Source.ordinaryRationalFromParsed right parsed₂
hunholdProposition4NegativeGlobal even left right leftNegative rightNegative k<m
    leftParse rightParse
  rewrite negativeParsedRationalIsNegMagnitude left parsed₁ leftNegative
        | negativeParsedRationalIsNegMagnitude right parsed₂ rightNegative =
  ℚP.neg-mono-<
    (Strict.parsedAnchorCodeStrictMagnitudeStrict parsed₂ parsed₁
      (negativeParsedCodeReverseStrict
        even left right leftNegative rightNegative k<m leftParse rightParse))
