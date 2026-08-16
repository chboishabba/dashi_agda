module DASHI.Arithmetic.DecimalDigitalRootNonaryExact where

------------------------------------------------------------------------
-- MATHEMATICAL CONTEXT
--
-- The familiar decimal digital-root rule is the positional-numeral
-- consequence of 10 = 1 (mod 9).  This module phrases that structurally:
-- whenever the base action becomes the identity in a quotient, positional
-- evaluation collapses exactly to the sum of digit images.
--
-- DASHI CONTRIBUTION
--
-- Specialise that principle to the repository's exact Z/9Z NonaryTruth ring.
-- Decimal digits are mapped to their residues, multiplication by the decimal
-- base is multiplication by residue 1, and the positional evaluator is proved
-- equal to the digit-sum evaluator for every finite digit list.
--
-- Positive digital roots 1..9 are then put in exact bijection with the nine
-- residues; roots {3,6,9} correspond exactly to residues {3,6,0}.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Foundations.Base369NonaryTruthRing as Ring

------------------------------------------------------------------------
-- Generic base-acts-as-one collapse theorem.
------------------------------------------------------------------------

record BaseOneAdditiveQuotient : Set₁ where
  field
    Carrier : Set
    zero : Carrier
    add : Carrier → Carrier → Carrier
    baseAction : Carrier → Carrier
    baseActsAsOne : (value : Carrier) → baseAction value ≡ value

open BaseOneAdditiveQuotient public

module BaseOneCollapse (Q : BaseOneAdditiveQuotient) where

  positionalValue : List (Carrier Q) → Carrier Q
  positionalValue [] = zero Q
  positionalValue (digit ∷ rest) =
    add Q digit (baseAction Q (positionalValue rest))

  digitSumValue : List (Carrier Q) → Carrier Q
  digitSumValue [] = zero Q
  digitSumValue (digit ∷ rest) =
    add Q digit (digitSumValue rest)

  positionalCollapsesToDigitSum :
    (digits : List (Carrier Q)) →
    positionalValue digits ≡ digitSumValue digits
  positionalCollapsesToDigitSum [] = refl
  positionalCollapsesToDigitSum (digit ∷ rest) =
    cong (add Q digit)
      (trans
        (baseActsAsOne Q (positionalValue rest))
        (positionalCollapsesToDigitSum rest))

------------------------------------------------------------------------
-- Decimal digits and the concrete Z/9Z quotient.
------------------------------------------------------------------------

data DecimalDigit : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : DecimalDigit

digitResidue9 : DecimalDigit → Ring.NonaryTruth
digitResidue9 d0 = Ring.non-0
digitResidue9 d1 = Ring.non-1
digitResidue9 d2 = Ring.non-2
digitResidue9 d3 = Ring.non-3
digitResidue9 d4 = Ring.non-4
digitResidue9 d5 = Ring.non-5
digitResidue9 d6 = Ring.non-6
digitResidue9 d7 = Ring.non-7
digitResidue9 d8 = Ring.non-8
digitResidue9 d9 = Ring.non-0

mulByDecimalBaseResidue : Ring.NonaryTruth → Ring.NonaryTruth
mulByDecimalBaseResidue value =
  Ring.nonaryMul Ring.nonaryOne value

decimalBaseActsAsOne :
  (value : Ring.NonaryTruth) →
  mulByDecimalBaseResidue value ≡ value
decimalBaseActsAsOne = Ring.nonaryMul-identityˡ

nonaryBaseOneQuotient : BaseOneAdditiveQuotient
nonaryBaseOneQuotient =
  record
    { Carrier = Ring.NonaryTruth
    ; zero = Ring.nonaryZero
    ; add = Ring.nonaryAdd
    ; baseAction = mulByDecimalBaseResidue
    ; baseActsAsOne = decimalBaseActsAsOne
    }

mapDigits : List DecimalDigit → List Ring.NonaryTruth
mapDigits [] = []
mapDigits (digit ∷ rest) = digitResidue9 digit ∷ mapDigits rest

open BaseOneCollapse nonaryBaseOneQuotient public
  renaming
    ( positionalValue to decimalPositionalResidue9
    ; digitSumValue to decimalDigitSumResidue9
    ; positionalCollapsesToDigitSum to decimalDigitSumInvariantMapped
    )

decimalDigitSumInvariant :
  (digits : List DecimalDigit) →
  decimalPositionalResidue9 (mapDigits digits)
  ≡ decimalDigitSumResidue9 (mapDigits digits)
decimalDigitSumInvariant digits =
  decimalDigitSumInvariantMapped (mapDigits digits)

------------------------------------------------------------------------
-- Positive digital roots and their exact residue classification.
------------------------------------------------------------------------

data PositiveDigitalRoot9 : Set where
  root1 root2 root3 root4 root5 root6 root7 root8 root9 :
    PositiveDigitalRoot9

rootResidue9 : PositiveDigitalRoot9 → Ring.NonaryTruth
rootResidue9 root1 = Ring.non-1
rootResidue9 root2 = Ring.non-2
rootResidue9 root3 = Ring.non-3
rootResidue9 root4 = Ring.non-4
rootResidue9 root5 = Ring.non-5
rootResidue9 root6 = Ring.non-6
rootResidue9 root7 = Ring.non-7
rootResidue9 root8 = Ring.non-8
rootResidue9 root9 = Ring.non-0

rootFromResidue9 : Ring.NonaryTruth → PositiveDigitalRoot9
rootFromResidue9 Ring.non-0 = root9
rootFromResidue9 Ring.non-1 = root1
rootFromResidue9 Ring.non-2 = root2
rootFromResidue9 Ring.non-3 = root3
rootFromResidue9 Ring.non-4 = root4
rootFromResidue9 Ring.non-5 = root5
rootFromResidue9 Ring.non-6 = root6
rootFromResidue9 Ring.non-7 = root7
rootFromResidue9 Ring.non-8 = root8

residueAfterRoot :
  (root : PositiveDigitalRoot9) →
  rootFromResidue9 (rootResidue9 root) ≡ root
residueAfterRoot root1 = refl
residueAfterRoot root2 = refl
residueAfterRoot root3 = refl
residueAfterRoot root4 = refl
residueAfterRoot root5 = refl
residueAfterRoot root6 = refl
residueAfterRoot root7 = refl
residueAfterRoot root8 = refl
residueAfterRoot root9 = refl

rootAfterResidue :
  (residue : Ring.NonaryTruth) →
  rootResidue9 (rootFromResidue9 residue) ≡ residue
rootAfterResidue Ring.non-0 = refl
rootAfterResidue Ring.non-1 = refl
rootAfterResidue Ring.non-2 = refl
rootAfterResidue Ring.non-3 = refl
rootAfterResidue Ring.non-4 = refl
rootAfterResidue Ring.non-5 = refl
rootAfterResidue Ring.non-6 = refl
rootAfterResidue Ring.non-7 = refl
rootAfterResidue Ring.non-8 = refl

data TriadicDigitalRoot : PositiveDigitalRoot9 → Set where
  root3IsTriadic : TriadicDigitalRoot root3
  root6IsTriadic : TriadicDigitalRoot root6
  root9IsTriadic : TriadicDigitalRoot root9

data TriadicNonaryResidue : Ring.NonaryTruth → Set where
  residue0IsTriadic : TriadicNonaryResidue Ring.non-0
  residue3IsTriadic : TriadicNonaryResidue Ring.non-3
  residue6IsTriadic : TriadicNonaryResidue Ring.non-6

triadicRootToResidue :
  (root : PositiveDigitalRoot9) →
  TriadicDigitalRoot root →
  TriadicNonaryResidue (rootResidue9 root)
triadicRootToResidue root3 root3IsTriadic = residue3IsTriadic
triadicRootToResidue root6 root6IsTriadic = residue6IsTriadic
triadicRootToResidue root9 root9IsTriadic = residue0IsTriadic

triadicResidueToRoot :
  (residue : Ring.NonaryTruth) →
  TriadicNonaryResidue residue →
  TriadicDigitalRoot (rootFromResidue9 residue)
triadicResidueToRoot Ring.non-0 residue0IsTriadic = root9IsTriadic
triadicResidueToRoot Ring.non-3 residue3IsTriadic = root3IsTriadic
triadicResidueToRoot Ring.non-6 residue6IsTriadic = root6IsTriadic

record DecimalDigitalRootNonaryEquivalence : Set where
  field
    rootToResidue : PositiveDigitalRoot9 → Ring.NonaryTruth
    residueToRoot : Ring.NonaryTruth → PositiveDigitalRoot9
    residueRootRoundTrip :
      (root : PositiveDigitalRoot9) →
      residueToRoot (rootToResidue root) ≡ root
    rootResidueRoundTrip :
      (residue : Ring.NonaryTruth) →
      rootToResidue (residueToRoot residue) ≡ residue

canonicalDecimalDigitalRootNonaryEquivalence :
  DecimalDigitalRootNonaryEquivalence
canonicalDecimalDigitalRootNonaryEquivalence =
  record
    { rootToResidue = rootResidue9
    ; residueToRoot = rootFromResidue9
    ; residueRootRoundTrip = residueAfterRoot
    ; rootResidueRoundTrip = rootAfterResidue
    }
