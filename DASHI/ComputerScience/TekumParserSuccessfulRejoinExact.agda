module DASHI.ComputerScience.TekumParserSuccessfulRejoinExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Base using (_++_)
open import Data.Vec.Properties using (reverse-injective)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSourceWordRoundTripExact as RoundTrip

------------------------------------------------------------------------
-- SUCCESSFUL SOURCE PARSING REJOINS TO THE EXACT INPUT ANCHOR
------------------------------------------------------------------------

decodeRegimeSound :
  ∀ {a b c r} →
  Regime.decodeRegime (Anchor.regime3 a b c) ≡ just r →
  (a ∷ b ∷ c ∷ []) ≡ RoundTrip.regimePrefixMSB r
decodeRegimeSound {Trit.neg} {Trit.neg} {Trit.neg} ()
decodeRegimeSound {Trit.neg} {Trit.neg} {Trit.zer} ()
decodeRegimeSound {Trit.neg} {Trit.neg} {Trit.pos} ()
decodeRegimeSound {Trit.neg} {Trit.zer} {Trit.neg} ()
decodeRegimeSound {Trit.neg} {Trit.zer} {Trit.zer} ()
decodeRegimeSound {Trit.neg} {Trit.zer} {Trit.pos} ()
decodeRegimeSound {Trit.neg} {Trit.pos} {Trit.neg} refl = refl
decodeRegimeSound {Trit.neg} {Trit.pos} {Trit.zer} refl = refl
decodeRegimeSound {Trit.neg} {Trit.pos} {Trit.pos} refl = refl
decodeRegimeSound {Trit.zer} {Trit.neg} {Trit.neg} refl = refl
decodeRegimeSound {Trit.zer} {Trit.neg} {Trit.zer} refl = refl
decodeRegimeSound {Trit.zer} {Trit.neg} {Trit.pos} refl = refl
decodeRegimeSound {Trit.zer} {Trit.zer} {Trit.neg} refl = refl
decodeRegimeSound {Trit.zer} {Trit.zer} {Trit.zer} refl = refl
decodeRegimeSound {Trit.zer} {Trit.zer} {Trit.pos} refl = refl
decodeRegimeSound {Trit.zer} {Trit.pos} {Trit.neg} refl = refl
decodeRegimeSound {Trit.zer} {Trit.pos} {Trit.zer} refl = refl
decodeRegimeSound {Trit.zer} {Trit.pos} {Trit.pos} refl = refl
decodeRegimeSound {Trit.pos} {Trit.neg} {Trit.neg} refl = refl
decodeRegimeSound {Trit.pos} {Trit.neg} {Trit.zer} refl = refl
decodeRegimeSound {Trit.pos} {Trit.neg} {Trit.pos} refl = refl
decodeRegimeSound {Trit.pos} {Trit.zer} {Trit.neg} ()
decodeRegimeSound {Trit.pos} {Trit.zer} {Trit.zer} ()
decodeRegimeSound {Trit.pos} {Trit.zer} {Trit.pos} ()
decodeRegimeSound {Trit.pos} {Trit.pos} {Trit.neg} ()
decodeRegimeSound {Trit.pos} {Trit.pos} {Trit.zer} ()
decodeRegimeSound {Trit.pos} {Trit.pos} {Trit.pos} ()

cong₂ :
  ∀ {A B C : Set} (f : A → B → C)
  {x x′ : A} {y y′ : B} →
  x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong₂ f refl refl = refl

parseAnchorMSBSuccessfulRejoin :
  ∀ {extra r payload parsed}
  (anchor : Vec Trit.Trit (8 + extra)) →
  Source.parseAnchorMSB anchor ≡ just (r , payload , parsed) →
  anchor ≡ RoundTrip.rejoinParsedAnchorMSB parsed
parseAnchorMSBSuccessfulRejoin (a ∷ b ∷ c ∷ payload₀) parseEq
  with Regime.decodeRegime (Anchor.regime3 a b c) in regimeEq
... | nothing with parseEq
...   | ()
... | just r′ with parseEq
...   | refl =
  cong₂ _++_
    (decodeRegimeSound regimeEq)
    (sym (RoundTrip.rejoinPayloadCorrect (Source.parsePayload r′ payload₀)))

parseOrdinaryAnchorSuccessfulRejoin :
  ∀ {extra r payload parsed}
  (word : Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  Source.anchorMSB word ≡ RoundTrip.rejoinParsedAnchorMSB parsed
parseOrdinaryAnchorSuccessfulRejoin word parseEq =
  parseAnchorMSBSuccessfulRejoin (Source.anchorMSB word) parseEq

successfulParseDeterminesConcreteAnchor :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂}
  (left right : Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  RoundTrip.rejoinParsedAnchorMSB parsed₁
    ≡ RoundTrip.rejoinParsedAnchorMSB parsed₂ →
  Fixed.concreteAnchor left ≡ Fixed.concreteAnchor right
successfulParseDeterminesConcreteAnchor left right leftParse rightParse rejoinEq =
  reverse-injective
    (trans
      (parseOrdinaryAnchorSuccessfulRejoin left leftParse)
      (trans rejoinEq
        (sym (parseOrdinaryAnchorSuccessfulRejoin right rightParse))))
