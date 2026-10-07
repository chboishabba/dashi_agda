module DASHI.ComputerScience.TekumProposition4PositiveGlobalExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Data.Integer.Base as ℤ using (+_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (_<_; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using (_<_)
import Data.Fin.Base as Fin using (toℕ)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedAnchorCodeExact as Code
import DASHI.ComputerScience.TekumParsedAnchorStrictOrderExact as Strict
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumPositiveAnchorInjectiveExact as Positive
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as Center
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- GLOBAL POSITIVE BRANCH OF HUNHOLD PROPOSITION 4
--
-- Corrected Definition-7 positive anchors have exact shifted rank
--
--   rank(anchor(word)) = sourceMagnitude + sourceCenterMagnitude.
--
-- Therefore arbitrary strict positive source-integer order is arbitrary strict
-- anchor-code order.  The direct radix-block theorem then gives strict exact
-- rational magnitude order, with no parser-totality or intermediate-chain
-- assumption.
------------------------------------------------------------------------

signOfPositiveWord :
  ∀ {n m} (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  Source.signOfWord word ≡ Anchor.positiveSign
signOfPositiveWord word valueEq
  rewrite valueEq = refl

positiveParsedRationalIsMagnitude :
  ∀ {extra r payload m}
  (word : Vec Trit.Trit (8 Agda.Builtin.Nat.+ extra))
  (parsed : Source.ParsedPayload extra r payload) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  Source.ordinaryRationalFromParsed word parsed
  ≡ Parsed.parsedMagnitude parsed
positiveParsedRationalIsMagnitude word parsed valueEq =
  trans
    (Parsed.parsedOrdinaryRationalIsSignedMagnitude word parsed)
    (cong
      (λ sign → Factor.applyRationalSign sign (Parsed.parsedMagnitude parsed))
      (signOfPositiveWord word valueEq))

positiveAnchorNatCode :
  ∀ {n m}
  (even : Width.EvenWidth n)
  (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  Positional.natCode (Fixed.concreteAnchor word)
  ≡ suc m + Center.sourceCenterMagnitudeAt even
positiveAnchorNatCode even word valueEq =
  trans
    (sym (Rank.rankToNatCode (Fixed.concreteAnchor word)))
    (Positive.positiveConcreteAnchorRank even word valueEq)

positiveSourceOrderRaisesAnchorCode :
  ∀ {n m k}
  (even : Width.EvenWidth n)
  (left right : Vec Trit.Trit n) →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc k) →
  m < k →
  Positional.natCode (Fixed.concreteAnchor left)
  < Positional.natCode (Fixed.concreteAnchor right)
positiveSourceOrderRaisesAnchorCode {m = m} {k = k}
    even left right leftPositive rightPositive m<k
  rewrite positiveAnchorNatCode even left leftPositive
        | positiveAnchorNatCode even right rightPositive =
  NatP.+-monoʳ-<
    (Center.sourceCenterMagnitudeAt even)
    (s≤s m<k)

positiveParsedCodeStrict :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂ m k}
  (even : Width.EvenWidth (8 Agda.Builtin.Nat.+ extra))
  (left right : Vec Trit.Trit (8 Agda.Builtin.Nat.+ extra)) →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc k) →
  m < k →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Code.parsedAnchorCode parsed₁ < Code.parsedAnchorCode parsed₂
positiveParsedCodeStrict even left right leftPositive rightPositive m<k
    leftParse rightParse
  rewrite sym (Code.successfulParseNatCode left leftParse)
        | sym (Code.successfulParseNatCode right rightParse) =
  positiveSourceOrderRaisesAnchorCode
    even left right leftPositive rightPositive m<k

hunholdProposition4PositiveGlobal :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂ m k}
  (even : Width.EvenWidth (8 Agda.Builtin.Nat.+ extra))
  (left right : Vec Trit.Trit (8 Agda.Builtin.Nat.+ extra)) →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc k) →
  m < k →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Source.ordinaryRationalFromParsed left parsed₁
    ℚ.< Source.ordinaryRationalFromParsed right parsed₂
hunholdProposition4PositiveGlobal even left right leftPositive rightPositive m<k
    leftParse rightParse
  rewrite positiveParsedRationalIsMagnitude left parsed₁ leftPositive
        | positiveParsedRationalIsMagnitude right parsed₂ rightPositive =
  Strict.parsedAnchorCodeStrictMagnitudeStrict parsed₁ parsed₂
    (positiveParsedCodeStrict
      even left right leftPositive rightPositive m<k leftParse rightParse)
