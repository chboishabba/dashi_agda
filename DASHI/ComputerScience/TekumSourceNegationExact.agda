module DASHI.ComputerScience.TekumSourceNegationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; -_)
open import Data.Maybe.Base as Maybe using (just; nothing; map)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_)
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
  cong Data.Vec.Base.reverse (Fixed.concreteAnchorNegationInvariant word)

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
-- SOURCE SPECIAL ENCODINGS UNDER WORD NEGATION
--
-- Hunhold Proposition 3 excludes NaR and infinity.  At the source-word level
-- negating all-positive gives all-negative and conversely, so the two reserved
-- encodings swap.  Keeping that fact separate prevents the semantic negation
-- map (which intentionally leaves non-finite constructors opaque) from being
-- misused as a theorem about the reserved source strings.
------------------------------------------------------------------------

invertAllNegative :
  ∀ {n} (xs : Vec Trit.Trit n) →
  Special.allSame Trit.neg xs ≡ Agda.Builtin.Bool.true →
  Special.allSame Trit.pos (BT.invertWord xs) ≡ Agda.Builtin.Bool.true
invertAllNegative [] evidence = refl
invertAllNegative (Trit.neg ∷ xs) evidence = invertAllNegative xs evidence
invertAllNegative (Trit.zer ∷ xs) ()
invertAllNegative (Trit.pos ∷ xs) ()

invertAllPositive :
  ∀ {n} (xs : Vec Trit.Trit n) →
  Special.allSame Trit.pos xs ≡ Agda.Builtin.Bool.true →
  Special.allSame Trit.neg (BT.invertWord xs) ≡ Agda.Builtin.Bool.true
invertAllPositive [] evidence = refl
invertAllPositive (Trit.neg ∷ xs) ()
invertAllPositive (Trit.zer ∷ xs) ()
invertAllPositive (Trit.pos ∷ xs) evidence = invertAllPositive xs evidence

------------------------------------------------------------------------
-- HUNHOLD PROP. 3, ON ITS ACTUAL DOMAIN.
--
-- The paper states the numerical negation proposition away from NaR and
-- infinity.  A successful ordinary parse is sufficient for that domain:
-- anchor/regime/exponent/fraction data are invariant and only the external
-- sign changes.
------------------------------------------------------------------------

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
