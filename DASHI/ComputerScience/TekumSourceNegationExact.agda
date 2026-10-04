module DASHI.ComputerScience.TekumSourceNegationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; -_)
open import Data.Maybe.Base using (just)
open import Data.Product using (_,_)
open import Data.Vec using (Vec)
open import Data.Vec.Base using (reverse)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- HUNHOLD PROP. 3 ON ITS SOURCE-STATED DOMAIN
--
-- The paper excludes NaR and infinity from Proposition 3.  We therefore keep
-- the load-bearing theorem on successful ordinary parser objects.  The two
-- reserved source strings are not smuggled through Sem.negateTekumValue.
------------------------------------------------------------------------

signOfIntegerNegation :
  (z : ℤ) →
  Source.signOfInteger (- z) ≡ Anchor.flipSign (Source.signOfInteger z)
signOfIntegerNegation (+ zero) = refl
signOfIntegerNegation (+ (suc n)) = refl
signOfIntegerNegation -[1+ n ] = refl

signOfInvertWord :
  ∀ {n} (word : Vec Trit.Trit n) →
  Source.signOfWord (BT.invertWord word)
  ≡ Anchor.flipSign (Source.signOfWord word)
signOfInvertWord word =
  trans
    (cong Source.signOfInteger (BT.toIntegerInvertWord word))
    (signOfIntegerNegation (BT.toInteger (BT.eval word)))

signOfNegateWord :
  ∀ {n} (word : Vec Trit.Trit n) →
  Source.signOfWord (Fixed.negateWord word)
  ≡ Anchor.flipSign (Source.signOfWord word)
signOfNegateWord word =
  trans
    (cong Source.signOfWord (Fixed.negateWordIsInvertWord word))
    (signOfInvertWord word)

anchorMSBNegationInvariant :
  ∀ {extra}
  (word : Vec Trit.Trit (8 + extra)) →
  Source.anchorMSB (Fixed.negateWord word) ≡ Source.anchorMSB word
anchorMSBNegationInvariant word =
  cong reverse (Fixed.concreteAnchorNegationInvariant word)

parseOrdinaryAnchorNegationInvariant :
  ∀ {extra}
  (word : Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor (Fixed.negateWord word)
  ≡ Source.parseOrdinaryAnchor word
parseOrdinaryAnchorNegationInvariant word =
  cong Source.parseAnchorMSB (anchorMSBNegationInvariant word)

ordinaryParsedNegation :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Sem.ordinary (Source.ordinaryFromParsed (Fixed.negateWord word) parsed)
  ≡ Sem.negateTekumValue
      (Sem.ordinary (Source.ordinaryFromParsed word parsed))
ordinaryParsedNegation word parsed
  rewrite signOfNegateWord word = refl

parseOrdinaryAnchorNegation :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  Source.parseOrdinaryAnchor (Fixed.negateWord word)
  ≡ just (r , payload , parsed)
parseOrdinaryAnchorNegation word parsed parseEq =
  trans (parseOrdinaryAnchorNegationInvariant word) parseEq

hunholdProposition3Ordinary :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Sem.ordinary (Source.ordinaryFromParsed (Fixed.negateWord word) parsed)
  ≡ Sem.negateTekumValue
      (Sem.ordinary (Source.ordinaryFromParsed word parsed))
hunholdProposition3Ordinary = ordinaryParsedNegation
