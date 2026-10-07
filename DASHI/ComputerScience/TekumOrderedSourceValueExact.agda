module DASHI.ComputerScience.TekumOrderedSourceValueExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _≤_; _<_; +<+; -<+; -<-)
import Data.Integer.Properties as ℤP
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (s≤s⁻¹)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Data.Vec.Base using (Vec; replicate)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryCenteredReconstructionExact as Centered
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumProposition4NegativeGlobalExact as Negative
import DASHI.ComputerScience.TekumProposition4PositiveGlobalExact as Positive
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSpecialIntegerOrderExact as SpecialOrder
import DASHI.ComputerScience.TekumSpecialValuesExact as Special
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- SOURCE-FAITHFUL ORDERED VALUE
--
-- NaR is the minimum reserved source code and infinity the maximum.  Zero is
-- the ordinary rational zero point.  Ordinary finite values delegate exactly
-- to the existing canonical Data.Rational.Base.ℚ decoder.
------------------------------------------------------------------------

data OrderedTekumValue : Set where
  orderedNaR : OrderedTekumValue
  orderedFinite : ℚ → OrderedTekumValue
  orderedInfinity : OrderedTekumValue

infix 4 _<ᵀ_
data _<ᵀ_ : OrderedTekumValue → OrderedTekumValue → Set where
  naRFinite : ∀ {q} → orderedNaR <ᵀ orderedFinite q
  naRInfinity : orderedNaR <ᵀ orderedInfinity
  finiteStrict : ∀ {p q} → p ℚ.< q → orderedFinite p <ᵀ orderedFinite q
  finiteInfinity : ∀ {q} → orderedFinite q <ᵀ orderedInfinity

data SourceOrderedDecode {extra}
    (word : Vec Trit.Trit (8 + extra)) : Set where
  decodedNaR :
    Special.classifySpecial word ≡ just Sem.naR →
    SourceOrderedDecode word
  decodedZero :
    Special.classifySpecial word ≡ just Sem.zeroValue →
    SourceOrderedDecode word
  decodedInfinity :
    Special.classifySpecial word ≡ just Sem.infinity →
    SourceOrderedDecode word
  decodedOrdinary :
    ∀ {r payload parsed} →
    Special.classifySpecial word ≡ nothing →
    Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
    SourceOrderedDecode word

orderedValue :
  ∀ {extra} {word : Vec Trit.Trit (8 + extra)} →
  SourceOrderedDecode word → OrderedTekumValue
orderedValue (decodedNaR _) = orderedNaR
orderedValue (decodedZero _) = orderedFinite 0ℚ
orderedValue (decodedInfinity _) = orderedInfinity
orderedValue {word = word} (decodedOrdinary {parsed = parsed} _ _) =
  orderedFinite (Source.ordinaryRationalFromParsed word parsed)

------------------------------------------------------------------------
-- WORD INTEGER RANGE / IMPOSSIBLE ORDINARY ZERO
------------------------------------------------------------------------

wordIntegerLower :
  ∀ {n} (word : Vec Trit.Trit n) →
  ℤ.- (+ (Positional.center n)) ≤ BT.toInteger (BT.eval word)
wordIntegerLower word =
  subst
    (ℤ.- (+ (Positional.center _)) ≤_)
    (Centered.centeredValueEncode word)
    (Centered.centeredValueLower (Centered.encodeCentered word))

wordIntegerUpper :
  ∀ {n} (word : Vec Trit.Trit n) →
  BT.toInteger (BT.eval word) ≤ + (Positional.center n)
wordIntegerUpper word =
  subst
    (_≤ + (Positional.center _))
    (Centered.centeredValueEncode word)
    (Centered.centeredValueUpper (Centered.encodeCentered word))

ordinaryZeroImpossible :
  ∀ {extra}
  (word : Vec Trit.Trit (8 + extra)) →
  Special.classifySpecial word ≡ nothing →
  BT.toInteger (BT.eval word) ≡ + 0 →
  ⊥
ordinaryZeroImpossible {extra} word ordinaryClass valueEq =
  impossible
  where
  zeroWord = replicate (8 + extra) Trit.zer

  wordIsZero : word ≡ zeroWord
  wordIsZero =
    Positional.toIntegerInjective
      (trans valueEq (sym (SpecialOrder.allZeroInteger (8 + extra))))

  impossibleEq : nothing ≡ just Sem.zeroValue
  impossibleEq =
    trans
      (sym ordinaryClass)
      (trans
        (cong Special.classifySpecial wordIsZero)
        (SpecialOrder.classifyAllZero (8 + extra)))

  impossible : ⊥
  impossible with impossibleEq
  ... | ()

------------------------------------------------------------------------
-- ORDINARY SIGN BOUNDARIES
------------------------------------------------------------------------

ordinaryNegativeBelowZero :
  ∀ {extra r payload parsed m}
  (word : Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  BT.toInteger (BT.eval word) ≡ -[1+ m ] →
  Source.ordinaryRationalFromParsed word parsed ℚ.< 0ℚ
ordinaryNegativeBelowZero word parseEq valueEq
  rewrite Negative.negativeParsedRationalIsNegMagnitude word parsed valueEq =
  ℚP.neg-mono-< (Parsed.parsedMagnitudePositive parsed)

ordinaryPositiveAboveZero :
  ∀ {extra r payload parsed m}
  (word : Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  0ℚ ℚ.< Source.ordinaryRationalFromParsed word parsed
ordinaryPositiveAboveZero word parseEq valueEq
  rewrite Positive.positiveParsedRationalIsMagnitude word parsed valueEq =
  Parsed.parsedMagnitudePositive parsed

ordinaryBeforeZero :
  ∀ {extra r payload parsed}
  (word : Vec Trit.Trit (8 + extra)) →
  Special.classifySpecial word ≡ nothing →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  BT.toInteger (BT.eval word) ℤ.< + 0 →
  Source.ordinaryRationalFromParsed word parsed ℚ.< 0ℚ
ordinaryBeforeZero word ordinaryClass parseEq integerLt
  with BT.toInteger (BT.eval word) in valueEq
... | + zero = ⊥-elim (ordinaryZeroImpossible word ordinaryClass valueEq)
... | + (suc n) with integerLt
...   | ()
... | -[1+ n ] = ordinaryNegativeBelowZero word parseEq valueEq

ordinaryAfterZero :
  ∀ {extra r payload parsed}
  (word : Vec Trit.Trit (8 + extra)) →
  Special.classifySpecial word ≡ nothing →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  (+ 0) ℤ.< BT.toInteger (BT.eval word) →
  0ℚ ℚ.< Source.ordinaryRationalFromParsed word parsed
ordinaryAfterZero word ordinaryClass parseEq integerLt
  with BT.toInteger (BT.eval word) in valueEq
... | + zero = ⊥-elim (ordinaryZeroImpossible word ordinaryClass valueEq)
... | + (suc n) = ordinaryPositiveAboveZero word parseEq valueEq
... | -[1+ n ] with integerLt
...   | ()

------------------------------------------------------------------------
-- ARBITRARY ORDINARY-ORDINARY INTEGER ORDER
------------------------------------------------------------------------

ordinaryIntegerStrict :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂}
  (even : Width.EvenWidth (8 + extra))
  (left right : Vec Trit.Trit (8 + extra)) →
  Special.classifySpecial left ≡ nothing →
  Special.classifySpecial right ≡ nothing →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  BT.toInteger (BT.eval left) ℤ.< BT.toInteger (BT.eval right) →
  Source.ordinaryRationalFromParsed left parsed₁
    ℚ.< Source.ordinaryRationalFromParsed right parsed₂
ordinaryIntegerStrict even left right leftClass rightClass leftParse rightParse integerLt
  with BT.toInteger (BT.eval left) in leftEq
     | BT.toInteger (BT.eval right) in rightEq
... | + zero | rightValue =
  ⊥-elim (ordinaryZeroImpossible left leftClass leftEq)
... | + (suc m) | + zero with integerLt
...   | ()
... | + (suc m) | + (suc k) with integerLt
...   | +<+ magnitudeLt =
      Positive.hunholdProposition4PositiveGlobal
        even left right leftEq rightEq (s≤s⁻¹ magnitudeLt) leftParse rightParse
... | + (suc m) | -[1+ k ] with integerLt
...   | ()
... | -[1+ m ] | + zero =
  ⊥-elim (ordinaryZeroImpossible right rightClass rightEq)
... | -[1+ m ] | + (suc k) =
  ℚP.<-trans
    (ordinaryNegativeBelowZero left leftParse leftEq)
    (ordinaryPositiveAboveZero right rightParse rightEq)
... | -[1+ m ] | -[1+ k ] with integerLt
...   | -<- k<m =
      Negative.hunholdProposition4NegativeGlobal
        even left right leftEq rightEq k<m leftParse rightParse

------------------------------------------------------------------------
-- SPECIAL ENDPOINT IMPOSSIBILITIES FROM THE CENTERED RANGE
------------------------------------------------------------------------

nothingBelowNaR :
  ∀ {n} (word : Vec Trit.Trit n) →
  ¬ (BT.toInteger (BT.eval word) ℤ.< ℤ.- (+ (Positional.center n)))
nothingBelowNaR word strict =
  ℤP.<-irrefl refl
    (ℤP.≤-<-trans (wordIntegerLower word) strict)

nothingAboveInfinity :
  ∀ {n} (word : Vec Trit.Trit n) →
  ¬ ((+ (Positional.center n)) ℤ.< BT.toInteger (BT.eval word))
nothingAboveInfinity word strict =
  ℤP.<-irrefl refl
    (ℤP.<-≤-trans strict (wordIntegerUpper word))

------------------------------------------------------------------------
-- FULL ORDER ON ANY SOURCE DECODES ALREADY KNOWN TO EXIST
------------------------------------------------------------------------

sourceIntegerStrictImpliesOrderedStrict :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra))
  {left right : Vec Trit.Trit (8 + extra)} →
  (leftDecode : SourceOrderedDecode left) →
  (rightDecode : SourceOrderedDecode right) →
  BT.toInteger (BT.eval left) ℤ.< BT.toInteger (BT.eval right) →
  orderedValue leftDecode <ᵀ orderedValue rightDecode
sourceIntegerStrictImpliesOrderedStrict even
    (decodedNaR leftNaR) (decodedNaR rightNaR) integerLt =
  ⊥-elim
    (ℤP.<-irrefl refl
      (subst
        (λ word → BT.toInteger (BT.eval left) ℤ.< BT.toInteger (BT.eval word))
        (sym (SpecialOrder.sameNaRWord leftNaR rightNaR))
        integerLt))
sourceIntegerStrictImpliesOrderedStrict even
    (decodedNaR leftNaR) (decodedZero rightZero) integerLt = naRFinite
sourceIntegerStrictImpliesOrderedStrict even
    (decodedNaR leftNaR) (decodedInfinity rightInfinity) integerLt = naRInfinity
sourceIntegerStrictImpliesOrderedStrict even
    (decodedNaR leftNaR) (decodedOrdinary rightClass rightParse) integerLt = naRFinite
sourceIntegerStrictImpliesOrderedStrict even
    (decodedZero leftZero) (decodedNaR rightNaR) integerLt =
  ⊥-elim
    (nothingBelowNaR _
      (subst
        (λ z → BT.toInteger (BT.eval _) ℤ.< z)
        (SpecialOrder.classifiedNaRInteger rightNaR)
        integerLt))
sourceIntegerStrictImpliesOrderedStrict even
    (decodedZero leftZero) (decodedZero rightZero) integerLt =
  ⊥-elim
    (ℤP.<-irrefl refl
      (subst
        (λ word → BT.toInteger (BT.eval _) ℤ.< BT.toInteger (BT.eval word))
        (sym (SpecialOrder.sameZeroWord leftZero rightZero))
        integerLt))
sourceIntegerStrictImpliesOrderedStrict even
    (decodedZero leftZero) (decodedInfinity rightInfinity) integerLt = finiteInfinity
sourceIntegerStrictImpliesOrderedStrict even {right = right}
    (decodedZero leftZero)
    (decodedOrdinary {parsed = parsed} rightClass rightParse) integerLt =
  finiteStrict
    (ordinaryAfterZero right rightClass rightParse
      (subst
        (λ z → z ℤ.< BT.toInteger (BT.eval right))
        (SpecialOrder.classifiedZeroInteger leftZero)
        integerLt))
sourceIntegerStrictImpliesOrderedStrict even {left = left}
    (decodedInfinity leftInfinity) rightDecode integerLt =
  ⊥-elim
    (nothingAboveInfinity _
      (subst
        (λ z → z ℤ.< BT.toInteger (BT.eval _))
        (SpecialOrder.classifiedInfinityInteger leftInfinity)
        integerLt))
sourceIntegerStrictImpliesOrderedStrict even {left = left}
    (decodedOrdinary {parsed = parsed} leftClass leftParse)
    (decodedNaR rightNaR) integerLt =
  ⊥-elim
    (nothingBelowNaR left
      (subst
        (λ z → BT.toInteger (BT.eval left) ℤ.< z)
        (SpecialOrder.classifiedNaRInteger rightNaR)
        integerLt))
sourceIntegerStrictImpliesOrderedStrict even {left = left}
    (decodedOrdinary {parsed = parsed} leftClass leftParse)
    (decodedZero rightZero) integerLt =
  finiteStrict
    (ordinaryBeforeZero left leftClass leftParse
      (subst
        (λ z → BT.toInteger (BT.eval left) ℤ.< z)
        (SpecialOrder.classifiedZeroInteger rightZero)
        integerLt))
sourceIntegerStrictImpliesOrderedStrict even
    (decodedOrdinary leftClass leftParse)
    (decodedInfinity rightInfinity) integerLt = finiteInfinity
sourceIntegerStrictImpliesOrderedStrict even {left = left} {right = right}
    (decodedOrdinary {parsed = leftParsed} leftClass leftParse)
    (decodedOrdinary {parsed = rightParsed} rightClass rightParse) integerLt =
  finiteStrict
    (ordinaryIntegerStrict
      even left right leftClass rightClass leftParse rightParse integerLt)
