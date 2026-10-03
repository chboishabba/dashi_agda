module DASHI.ComputerScience.TekumSourceWordDecodeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Rational.Base using (ℚ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Base using (reverse; _++_; cast)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSpecialValuesExact as Special
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed

------------------------------------------------------------------------
-- SOURCE ORIENTATION
------------------------------------------------------------------------

signOfInteger : ℤ → Anchor.TekumSign
signOfInteger (+ zero) = Anchor.zeroSign
signOfInteger (+ (suc n)) = Anchor.positiveSign
signOfInteger -[1+ n ] = Anchor.negativeSign

signOfWord : ∀ {n} → Vec Trit.Trit n → Anchor.TekumSign
signOfWord word = signOfInteger (BT.toInteger (BT.eval word))

integerToIntCode : ℤ → Sem.IntCode
integerToIntCode (+ n) = Sem.nonnegative n
integerToIntCode -[1+ n ] = Sem.negative (suc n)

integerToIntCodeRoundTrip :
  (z : ℤ) → Exact.intCodeToInteger (integerToIntCode z) ≡ z
integerToIntCodeRoundTrip (+ zero) = refl
integerToIntCodeRoundTrip (+ (suc n)) = refl
integerToIntCodeRoundTrip -[1+ n ] = refl

addIntCode : Sem.IntCode → Sem.IntCode → Sem.IntCode
addIntCode x y =
  integerToIntCode (Exact.intCodeToInteger x ℤ.+ Exact.intCodeToInteger y)

addIntCodeInteger :
  (x y : Sem.IntCode) →
  Exact.intCodeToInteger (addIntCode x y)
  ≡ Exact.intCodeToInteger x ℤ.+ Exact.intCodeToInteger y
addIntCodeInteger x y = integerToIntCodeRoundTrip _

anchorMSB :
  ∀ {extra} →
  Vec Trit.Trit (8 + extra) →
  Vec Trit.Trit (8 + extra)
anchorMSB word = reverse (Fixed.concreteAnchor word)

------------------------------------------------------------------------
-- Exact dependent field split for every source regime.
------------------------------------------------------------------------

record ParsedPayload
    (extra : Nat)
    (r : Regime.RegimeCode)
    (payload : Vec Trit.Trit (5 + extra)) : Set where
  constructor parsedPayload
  field
    exponentMSB : Vec Trit.Trit (Regime.exponentCount r)
    fractionMSB : Vec Trit.Trit (Regime.fractionCount (8 + extra) r)
    fieldLength :
      Regime.exponentCount r + Regime.fractionCount (8 + extra) r
      ≡ 5 + extra
    payloadJoin :
      payload ≡ cast fieldLength (exponentMSB ++ fractionMSB)
open ParsedPayload public

parsePayload :
  ∀ {extra}
  (r : Regime.RegimeCode)
  (payload : Vec Trit.Trit (5 + extra)) →
  ParsedPayload extra r payload
parsePayload Regime.rm7 (a ∷ b ∷ c ∷ d ∷ e ∷ rest) =
  parsedPayload (a ∷ b ∷ c ∷ d ∷ e ∷ []) rest refl refl
parsePayload Regime.rm6 (a ∷ b ∷ c ∷ d ∷ rest) =
  parsedPayload (a ∷ b ∷ c ∷ d ∷ []) rest refl refl
parsePayload Regime.rm5 (a ∷ b ∷ c ∷ rest) =
  parsedPayload (a ∷ b ∷ c ∷ []) rest refl refl
parsePayload Regime.rm4 (a ∷ b ∷ rest) =
  parsedPayload (a ∷ b ∷ []) rest refl refl
parsePayload Regime.rm3 (a ∷ rest) =
  parsedPayload (a ∷ []) rest refl refl
parsePayload Regime.rm2 payload = parsedPayload [] payload refl refl
parsePayload Regime.rm1 payload = parsedPayload [] payload refl refl
parsePayload Regime.r0 payload = parsedPayload [] payload refl refl
parsePayload Regime.rp1 payload = parsedPayload [] payload refl refl
parsePayload Regime.rp2 payload = parsedPayload [] payload refl refl
parsePayload Regime.rp3 (a ∷ rest) =
  parsedPayload (a ∷ []) rest refl refl
parsePayload Regime.rp4 (a ∷ b ∷ rest) =
  parsedPayload (a ∷ b ∷ []) rest refl refl
parsePayload Regime.rp5 (a ∷ b ∷ c ∷ rest) =
  parsedPayload (a ∷ b ∷ c ∷ []) rest refl refl
parsePayload Regime.rp6 (a ∷ b ∷ c ∷ d ∷ rest) =
  parsedPayload (a ∷ b ∷ c ∷ d ∷ []) rest refl refl
parsePayload Regime.rp7 (a ∷ b ∷ c ∷ d ∷ e ∷ rest) =
  parsedPayload (a ∷ b ∷ c ∷ d ∷ e ∷ []) rest refl refl

exponentLST :
  ∀ {extra r payload} →
  ParsedPayload extra r payload →
  Vec Trit.Trit (Regime.exponentCount r)
exponentLST parsed = reverse (exponentMSB parsed)

fractionLST :
  ∀ {extra r payload} →
  ParsedPayload extra r payload →
  Vec Trit.Trit (Regime.fractionCount (8 + extra) r)
fractionLST parsed = reverse (fractionMSB parsed)

ParsedOrdinaryAnchor : Nat → Set
ParsedOrdinaryAnchor extra =
  Σ Regime.RegimeCode λ r →
  Σ (Vec Trit.Trit (5 + extra)) λ payload →
  ParsedPayload extra r payload

parseAnchorMSB :
  ∀ {extra} →
  Vec Trit.Trit (8 + extra) →
  Maybe (ParsedOrdinaryAnchor extra)
parseAnchorMSB (r2 ∷ r1 ∷ r0 ∷ payload)
  with Regime.decodeRegime (Anchor.regime3 r2 r1 r0)
... | nothing = nothing
... | just r = just (r , payload , parsePayload r payload)

parseOrdinaryAnchor :
  ∀ {extra} →
  Vec Trit.Trit (8 + extra) →
  Maybe (ParsedOrdinaryAnchor extra)
parseOrdinaryAnchor word = parseAnchorMSB (anchorMSB word)

------------------------------------------------------------------------
-- Definition 8 equations (9), (14), and (15), on exact integer carriers.
------------------------------------------------------------------------

exponentIntCode :
  ∀ {extra r payload} →
  ParsedPayload extra r payload →
  Sem.IntCode
exponentIntCode {r = r} parsed =
  addIntCode
    (integerToIntCode (BT.toInteger (BT.eval (exponentLST parsed))))
    (Regime.bias r)

exponentIntCodeInteger :
  ∀ {extra r payload}
  (parsed : ParsedPayload extra r payload) →
  Exact.intCodeToInteger (exponentIntCode parsed)
  ≡ BT.toInteger (BT.eval (exponentLST parsed))
      ℤ.+ Exact.intCodeToInteger (Regime.bias r)
exponentIntCodeInteger {r = r} parsed =
  addIntCodeInteger
    (integerToIntCode (BT.toInteger (BT.eval (exponentLST parsed))))
    (Regime.bias r)

fractionIntCode :
  ∀ {extra r payload} →
  ParsedPayload extra r payload →
  Sem.IntCode
fractionIntCode parsed =
  integerToIntCode (BT.toInteger (BT.eval (fractionLST parsed)))

fractionIntCodeInteger :
  ∀ {extra r payload}
  (parsed : ParsedPayload extra r payload) →
  Exact.intCodeToInteger (fractionIntCode parsed)
  ≡ BT.toInteger (BT.eval (fractionLST parsed))
fractionIntCodeInteger parsed = integerToIntCodeRoundTrip _

ordinaryFromParsed :
  ∀ {extra r payload} →
  Vec Trit.Trit (8 + extra) →
  ParsedPayload extra r payload →
  Sem.OrdinaryTekum
ordinaryFromParsed {extra} {r = r} word parsed =
  Sem.ordinaryTekum
    (signOfWord word)
    (exponentIntCode parsed)
    (fractionIntCode parsed)
    (Regime.fractionCount (8 + extra) r)

ordinaryRationalFromParsed :
  ∀ {extra r payload} →
  (word : Vec Trit.Trit (8 + extra)) →
  (parsed : ParsedPayload extra r payload) →
  ℚ
ordinaryRationalFromParsed word parsed =
  Exact.ordinaryRational (ordinaryFromParsed word parsed)

------------------------------------------------------------------------
-- Complete source decoder.
--
-- Hunhold reserves the SOURCE strings T...T, 0...0 and 1...1 for NaR, zero
-- and infinity.  Classification therefore happens before anchoring.  The
-- anchor is only the ordinary-field coordinate chart.
------------------------------------------------------------------------

parseTekumWord :
  ∀ {extra} →
  Vec Trit.Trit (8 + extra) →
  Maybe Sem.TekumValue
parseTekumWord word with Special.classifySpecial word
... | just specialValue = just (Sem.special specialValue)
... | nothing with parseOrdinaryAnchor word
...   | nothing = nothing
...   | just (r , payload , parsed) =
  just (Sem.ordinary (ordinaryFromParsed word parsed))

decodeNormalWidthTekumWord :
  ∀ {extra} →
  Vec Trit.Trit (8 + extra) →
  Maybe Sem.TekumValue
decodeNormalWidthTekumWord = parseTekumWord

record SourceFieldOrderBoundary : Set where
  constructor sourceFieldOrderBoundary
  field
    sourceAnchorReadMostSignificantFirst : Bool
    repositoryIntegerFieldsReadLeastSignificantFirst : Bool
    parserReversesAnchorExactlyOnce : Bool
    parserReversesEachNumericFieldBeforeIntegerDecode : Bool
    specialClassificationAppliedToSourceWord : Bool
    parityRestrictionProvedInThisOwner : Bool

normalWidthParserUsesSourceFieldOrder : SourceFieldOrderBoundary
normalWidthParserUsesSourceFieldOrder =
  sourceFieldOrderBoundary true true true true true false
