module DASHI.ComputerScience.TekumSourceNegationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; -_)
open import Data.Maybe.Base as Maybe using (just; nothing; map)
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
import DASHI.ComputerScience.TekumSpecialValuesExact as Special

------------------------------------------------------------------------
-- INTEGER SIGN NEGATION
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

------------------------------------------------------------------------
-- THE ANCHOR/PAYLOAD IS NEGATION-INVARIANT
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- ORDINARY SOURCE DATA CHANGES ONLY IN THE EXTERNAL SIGN.
------------------------------------------------------------------------

ordinaryParsedNegation :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Sem.ordinary (Source.ordinaryFromParsed (Fixed.negateWord word) parsed)
  ≡ Sem.negateTekumValue
      (Sem.ordinary (Source.ordinaryFromParsed word parsed))
ordinaryParsedNegation word parsed
  rewrite signOfNegateWord word = refl

------------------------------------------------------------------------
-- HUNHOLD PROP. 3, AT THE COMPLETE SOURCE PARSER SURFACE.
--
-- Specials are fixed by Sem.negateTekumValue exactly as encoded by the
-- current source convention; ordinary values retain their anchor fields and
-- flip only their external sign.
------------------------------------------------------------------------

parseTekumWordNegation :
  ∀ {extra}
  (word : Vec Trit.Trit (8 + extra)) →
  Source.parseTekumWord (Fixed.negateWord word)
  ≡ Maybe.map Sem.negateTekumValue (Source.parseTekumWord word)
parseTekumWordNegation word
  rewrite Fixed.concreteAnchorNegationInvariant word
  with Special.classifySpecial (Fixed.concreteAnchor word)
... | just specialValue = refl
... | nothing
  rewrite parseOrdinaryAnchorNegationInvariant word
  with Source.parseOrdinaryAnchor word
...   | nothing = refl
...   | just (r , payload , parsed)
  rewrite signOfNegateWord word = refl
