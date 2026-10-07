module DASHI.ComputerScience.TekumSourceAnchorRegimeBandExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (+_; -[1+_])
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryCenteredReconstructionExact as Centered
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedAnchorListExact as AnchorList
import DASHI.ComputerScience.TekumPositiveAnchorInjectiveExact as PositiveAnchor
import DASHI.ComputerScience.TekumProposition4NegativeGlobalExact as NegativeGlobal
import DASHI.ComputerScience.TekumProposition4PositiveGlobalExact as PositiveGlobal
import DASHI.ComputerScience.TekumRawAnchorRegimeBandExact as Raw
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as SourceCenter
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSpecialIntegerOrderExact as SpecialOrder
import DASHI.ComputerScience.TekumSpecialValuesExact as Special
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- 4c + 1 = 27P AT CORE WIDTH n = 8 + extra
------------------------------------------------------------------------

widthPowerAsTwentySevenPayloadScale :
  (extra : Nat) →
  BT.pow3 (8 + extra) ≡ 27 * Raw.payloadScale extra
widthPowerAsTwentySevenPayloadScale extra =
  Factor.balancedPow3Add 3 (5 + extra)

fourCenterMagnitudePlusOne :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra)) →
  4 * SourceCenter.sourceCenterMagnitudeAt even + 1
  ≡ 27 * Raw.payloadScale extra
fourCenterMagnitudePlusOne {extra} even =
  trans
    normalizedCenter
    (widthPowerAsTwentySevenPayloadScale extra)
  where
  c = SourceCenter.sourceCenterMagnitudeAt even

  normalizedCenter : 4 * c + 1 ≡ BT.pow3 (8 + extra)
  normalizedCenter
    rewrite sym (Centered.twiceCenterPlusOne (8 + extra))
          | SourceCenter.centerAtEvenWidth even =
    solve 1
      (λ x → (con 4 :* x) :+ con 1 := (con 2 :* (con 2 :* x)) :+ con 1)
      refl c

payloadScaleAtLeastOne :
  (extra : Nat) → 1 ≤ Raw.payloadScale extra
payloadScaleAtLeastOne extra =
  subst
    (1 ≤_)
    (Centered.twiceCenterPlusOne (5 + extra))
    (NatP.m≤n+m 1 (2 * Positional.center (5 + extra)))

sixPayloadScaleBelowCenterMagnitude :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra)) →
  6 * Raw.payloadScale extra
  ≤ SourceCenter.sourceCenterMagnitudeAt even
sixPayloadScaleBelowCenterMagnitude {extra} even =
  NatP.*-cancelˡ-≤ 4 sixP c fourScaled
  where
  p = Raw.payloadScale extra
  c = SourceCenter.sourceCenterMagnitudeAt even

  one≤threeP : 1 ≤ 3 * p
  one≤threeP =
    NatP.≤-trans
      (payloadScaleAtLeastOne extra)
      (subst
        (p ≤_)
        (solve 1 (λ x → x :+ (con 2 :* x) := con 3 :* x) refl p)
        (NatP.m≤m+n p (2 * p)))

  twentyFourPPlusOneBelowTwentySevenP :
    24 * p + 1 ≤ 27 * p
  twentyFourPPlusOneBelowTwentySevenP =
    subst
      (24 * p + 1 ≤_)
      (solve 1 (λ x → (con 24 :* x) :+ (con 3 :* x) := con 27 :* x) refl p)
      (NatP.+-monoˡ-≤ (24 * p) one≤threeP)

  twentyFourPPlusOneBelowFourCPlusOne :
    24 * p + 1 ≤ 4 * c + 1
  twentyFourPPlusOneBelowFourCPlusOne =
    subst
      (24 * p + 1 ≤_)
      (sym (fourCenterMagnitudePlusOne even))
      twentyFourPPlusOneBelowTwentySevenP

  twentyFourPBelowFourC : 24 * p ≤ 4 * c
  twentyFourPBelowFourC =
    NatP.+-cancelʳ-≤ (24 * p) (4 * c) 1
      twentyFourPPlusOneBelowFourCPlusOne

  sixP = 6 * p

  fourScaled : 4 * sixP ≤ 4 * c
  fourScaled =
    subst
      (_≤ 4 * c)
      (solve 1 (λ x → con 4 :* (con 6 :* x) := con 24 :* x) refl p)
      twentyFourPBelowFourC

threeCenterMagnitudeBelowTwentyOnePayloadScale :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra)) →
  3 * SourceCenter.sourceCenterMagnitudeAt even
  < 21 * Raw.payloadScale extra
threeCenterMagnitudeBelowTwentyOnePayloadScale {extra} even =
  NatP.*-cancelˡ-< 4 (3 * c) (21 * p) scaledStrict
  where
  p = Raw.payloadScale extra
  c = SourceCenter.sourceCenterMagnitudeAt even

  tripleIdentity : 12 * c + 3 ≡ 81 * p
  tripleIdentity =
    trans
      (solve 1
        (λ x → (con 12 :* x) :+ con 3 := con 3 :* ((con 4 :* x) :+ con 1))
        refl c)
      (trans
        (cong (3 *_) (fourCenterMagnitudePlusOne even))
        (solve 1 (λ x → con 3 :* (con 27 :* x) := con 81 :* x) refl p))

  twelveCBelowEightyOneP : 12 * c < 81 * p
  twelveCBelowEightyOneP =
    subst
      (12 * c <_)
      tripleIdentity
      (NatP.m<m+n (12 * c) (s≤s (s≤s (s≤s z≤n))))

  eightyOnePBelowEightyFourP : 81 * p ≤ 84 * p
  eightyOnePBelowEightyFourP =
    NatP.*-mono-≤ (NatP.m≤m+n 81 3) NatP.≤-refl

  twelveCBelowEightyFourP : 12 * c < 84 * p
  twelveCBelowEightyFourP =
    NatP.<-≤-trans twelveCBelowEightyOneP eightyOnePBelowEightyFourP

  scaledStrict : 4 * (3 * c) < 4 * (21 * p)
  scaledStrict =
    subst
      (λ left → left < 4 * (21 * p))
      (solve 1 (λ x → con 4 :* (con 3 :* x) := con 12 :* x) refl c)
      (subst
        (12 * c <_)
        (sym (solve 1 (λ x → con 4 :* (con 21 :* x) := con 84 :* x) refl p))
        twelveCBelowEightyFourP)

------------------------------------------------------------------------
-- NON-SPECIAL SOURCE WORDS HAVE NONZERO INTEGER VALUE
------------------------------------------------------------------------

nonSpecialZeroImpossible :
  ∀ {extra}
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  Special.classifySpecial word ≡ nothing →
  BT.toInteger (BT.eval word) ≡ + 0 →
  ⊥
nonSpecialZeroImpossible {extra} word nonSpecial zeroEq =
  contradiction
  where
  zeroWord = Vec.replicate (8 + extra) Trit.zer

  wordEq : word ≡ zeroWord
  wordEq =
    Positional.toIntegerInjective
      (trans zeroEq (sym (SpecialOrder.allZeroInteger (8 + extra))))

  contradictionEq : nothing ≡ Data.Maybe.Base.just DASHI.ComputerScience.TekumFiniteSemanticsExact.zeroValue
  contradictionEq =
    trans
      (sym nonSpecial)
      (trans
        (cong Special.classifySpecial wordEq)
        (SpecialOrder.classifyAllZero (8 + extra)))

  contradiction : ⊥
  contradiction with contradictionEq
  ... | ()

------------------------------------------------------------------------
-- CORRECTED SOURCE ANCHOR LIES IN WHOLE-CODE REGIME BAND 6..20
------------------------------------------------------------------------

anchorNatCodeBandForPositive :
  ∀ {extra m}
  (even : Width.EvenWidth (8 + extra))
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  BT.toInteger (BT.eval word) ≡ + (suc m) →
  (6 * Raw.payloadScale extra
    ≤ Positional.natCode (Fixed.concreteAnchor word))
  Data.Product.Base.×
  (Positional.natCode (Fixed.concreteAnchor word)
    < 21 * Raw.payloadScale extra)
anchorNatCodeBandForPositive {extra} {m} even word positiveEq =
  lower , upper
  where
  c = SourceCenter.sourceCenterMagnitudeAt even

  anchorEq :
    Positional.natCode (Fixed.concreteAnchor word) ≡ suc m + c
  anchorEq = PositiveGlobal.positiveAnchorNatCode even word positiveEq

  lower : 6 * Raw.payloadScale extra ≤ Positional.natCode (Fixed.concreteAnchor word)
  lower =
    subst
      (6 * Raw.payloadScale extra ≤_)
      (sym anchorEq)
      (NatP.≤-trans
        (sixPayloadScaleBelowCenterMagnitude even)
        (NatP.m≤n+m c (suc m)))

  magnitudeBound : suc m ≤ 2 * c
  magnitudeBound =
    subst
      (suc m ≤_)
      (SourceCenter.centerAtEvenWidth even)
      (PositiveAnchor.positiveMagnitudeBound word positiveEq)

  anchorBelowThreeC : suc m + c ≤ 3 * c
  anchorBelowThreeC =
    subst
      (suc m + c ≤_)
      (solve 1 (λ x → (con 2 :* x) :+ x := con 3 :* x) refl c)
      (NatP.+-monoʳ-≤ c magnitudeBound)

  upper : Positional.natCode (Fixed.concreteAnchor word) < 21 * Raw.payloadScale extra
  upper =
    subst
      (_< 21 * Raw.payloadScale extra)
      (sym anchorEq)
      (NatP.≤-<-trans
        anchorBelowThreeC
        (threeCenterMagnitudeBelowTwentyOnePayloadScale even))

anchorNatCodeBandForNegative :
  ∀ {extra m}
  (even : Width.EvenWidth (8 + extra))
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  BT.toInteger (BT.eval word) ≡ -[1+ m ] →
  (6 * Raw.payloadScale extra
    ≤ Positional.natCode (Fixed.concreteAnchor word))
  Data.Product.Base.×
  (Positional.natCode (Fixed.concreteAnchor word)
    < 21 * Raw.payloadScale extra)
anchorNatCodeBandForNegative {extra} even word negativeEq
  rewrite NegativeGlobal.negativeAnchorNatCode even word negativeEq =
  let positiveWord = Fixed.negateWord word in
  anchorNatCodeBandForPositive
    even positiveWord
    (NegativeGlobal.negatedNegativeIsPositive word negativeEq)

rawAnchorCodeIsConcreteNatCode :
  ∀ {extra} (word : Vec.Vec Trit.Trit (8 + extra)) →
  Raw.rawAnchorCode (Source.anchorMSB word)
  ≡ Positional.natCode (Fixed.concreteAnchor word)
rawAnchorCodeIsConcreteNatCode word =
  trans
    (cong Code.listCode (AnchorList.anchorMSBReverseToSourceList word))
    (Code.listCodeToNatCode (Fixed.concreteAnchor word))

nonSpecialAnchorBand :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra))
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  Special.classifySpecial word ≡ nothing →
  (6 * Raw.payloadScale extra ≤ Raw.rawAnchorCode (Source.anchorMSB word))
  Data.Product.Base.×
  (Raw.rawAnchorCode (Source.anchorMSB word) < 21 * Raw.payloadScale extra)
nonSpecialAnchorBand {extra} even word nonSpecial
  with BT.toInteger (BT.eval word) in valueEq
... | + 0 = ⊥-elim (nonSpecialZeroImpossible word nonSpecial valueEq)
... | + (suc m) =
  transportBand
    (anchorNatCodeBandForPositive even word valueEq)
... | -[1+ m ] =
  transportBand
    (anchorNatCodeBandForNegative even word valueEq)
  where
  transportBand :
    (6 * Raw.payloadScale extra ≤ Positional.natCode (Fixed.concreteAnchor word))
    Data.Product.Base.×
    (Positional.natCode (Fixed.concreteAnchor word) < 21 * Raw.payloadScale extra) →
    (6 * Raw.payloadScale extra ≤ Raw.rawAnchorCode (Source.anchorMSB word))
    Data.Product.Base.×
    (Raw.rawAnchorCode (Source.anchorMSB word) < 21 * Raw.payloadScale extra)
  transportBand (lower , upper)
    rewrite rawAnchorCodeIsConcreteNatCode word = lower , upper
