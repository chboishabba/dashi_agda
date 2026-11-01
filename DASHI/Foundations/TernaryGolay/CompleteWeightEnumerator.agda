module DASHI.Foundations.TernaryGolay.CompleteWeightEnumerator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_+_)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high )
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.CodeBoundary as Boundary
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Complete three-symbol weight enumerator.
--
-- A composition (n0,n1,n2) records the exact number of zero, one and two
-- symbols in a codeword, not just its Hamming weight.  All coefficients below
-- reduce over the explicit list of 729 codewords.
------------------------------------------------------------------------

symbolContribution : TriTruth → TriTruth → Nat
symbolContribution expected actual with Explicit.triEq expected actual
... | true = 1
... | false = 0

countSymbol : TriTruth → Boundary.Word12 → Nat
countSymbol symbol word =
  symbolContribution symbol (Boundary.e0 word) +
  symbolContribution symbol (Boundary.e1 word) +
  symbolContribution symbol (Boundary.e2 word) +
  symbolContribution symbol (Boundary.e3 word) +
  symbolContribution symbol (Boundary.e4 word) +
  symbolContribution symbol (Boundary.e5 word) +
  symbolContribution symbol (Boundary.e6 word) +
  symbolContribution symbol (Boundary.e7 word) +
  symbolContribution symbol (Boundary.e8 word) +
  symbolContribution symbol (Boundary.e9 word) +
  symbolContribution symbol (Boundary.e10 word) +
  symbolContribution symbol (Boundary.e11 word)

record Composition012 : Set where
  constructor composition012
  field
    zeroSymbols : Nat
    oneSymbols : Nat
    twoSymbols : Nat

open Composition012 public

compositionOf : Boundary.Word12 → Composition012
compositionOf word =
  composition012
    (countSymbol tri-low word)
    (countSymbol tri-mid word)
    (countSymbol tri-high word)

compositionEq : Composition012 → Composition012 → Bool
compositionEq left right =
  Explicit._&&_
    (Explicit.natEq (zeroSymbols left) (zeroSymbols right))
    (Explicit._&&_
      (Explicit.natEq (oneSymbols left) (oneSymbols right))
      (Explicit.natEq (twoSymbols left) (twoSymbols right)))

countComposition :
  Composition012 →
  List Boundary.Word12 →
  Nat
countComposition target [] = zero
countComposition target (word ∷ words)
  with compositionEq target (compositionOf word)
... | true =
  suc (countComposition target words)
... | false =
  countComposition target words

c1200 c660 c606 c633 c363 c336 c0120 c066 c0012 :
  Composition012
c1200 = composition012 12 0 0
c660 = composition012 6 6 0
c606 = composition012 6 0 6
c633 = composition012 6 3 3
c363 = composition012 3 6 3
c336 = composition012 3 3 6
c0120 = composition012 0 12 0
c066 = composition012 0 6 6
c0012 = composition012 0 0 12

coefficient1200 :
  countComposition c1200 Explicit.allCodewords ≡ 1
coefficient1200 = refl

coefficient660 :
  countComposition c660 Explicit.allCodewords ≡ 22
coefficient660 = refl

coefficient606 :
  countComposition c606 Explicit.allCodewords ≡ 22
coefficient606 = refl

coefficient633 :
  countComposition c633 Explicit.allCodewords ≡ 220
coefficient633 = refl

coefficient363 :
  countComposition c363 Explicit.allCodewords ≡ 220
coefficient363 = refl

coefficient336 :
  countComposition c336 Explicit.allCodewords ≡ 220
coefficient336 = refl

coefficient0120 :
  countComposition c0120 Explicit.allCodewords ≡ 1
coefficient0120 = refl

coefficient066 :
  countComposition c066 Explicit.allCodewords ≡ 22
coefficient066 = refl

coefficient0012 :
  countComposition c0012 Explicit.allCodewords ≡ 1
coefficient0012 = refl

completeCoefficientSum :
  1 + 22 + 22 + 220 + 220 + 220 + 1 + 22 + 1 ≡ 729
completeCoefficientSum = refl

record CompleteWeightEnumeratorCertificate : Set where
  constructor completeWeightEnumeratorCertificate
  field
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String
    zeroWordCoefficient : countComposition c1200 Explicit.allCodewords ≡ 1
    sixSixZeroCoefficient : countComposition c660 Explicit.allCodewords ≡ 22
    sixZeroSixCoefficient : countComposition c606 Explicit.allCodewords ≡ 22
    sixThreeThreeCoefficient : countComposition c633 Explicit.allCodewords ≡ 220
    threeSixThreeCoefficient : countComposition c363 Explicit.allCodewords ≡ 220
    threeThreeSixCoefficient : countComposition c336 Explicit.allCodewords ≡ 220
    allOneCoefficient : countComposition c0120 Explicit.allCodewords ≡ 1
    sixOneSixTwoCoefficient : countComposition c066 Explicit.allCodewords ≡ 22
    allTwoCoefficient : countComposition c0012 Explicit.allCodewords ≡ 1
    total : 1 + 22 + 22 + 220 + 220 + 220 + 1 + 22 + 1 ≡ 729

canonicalCompleteWeightEnumerator : CompleteWeightEnumeratorCertificate
canonicalCompleteWeightEnumerator =
  completeWeightEnumeratorCertificate
    (Sources.author Sources.macWilliamsMallowsSloaneGleasonEntry)
    (Sources.title Sources.macWilliamsMallowsSloaneGleasonEntry)
    "10.1109/TIT.1972.1054898"
    coefficient1200
    coefficient660
    coefficient606
    coefficient633
    coefficient363
    coefficient336
    coefficient0120
    coefficient066
    coefficient0012
    completeCoefficientSum

completeWeightEnumeratorReceipt : GenericReceipt.GenericReceipt
completeWeightEnumeratorReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "ternary Golay complete weight enumerator"
    "DASHI.Foundations.TernaryGolay.CompleteWeightEnumerator"
    "canonicalCompleteWeightEnumerator"
    "all nine nonzero three-symbol composition coefficients are recomputed over the explicit 729-word code, refining the Hamming enumerator and exposing the one/two symmetry used by monomial automorphisms"
    "the invariant-theory citation calibrates the result but does not replace the finite Agda computation"
    "agda -i . DASHI/Foundations/TernaryGolay/CompleteWeightEnumerator.agda"

completeWeightEnumeratorReceiptNonPromoting :
  GenericReceipt.promotesClaim completeWeightEnumeratorReceipt ≡ false
completeWeightEnumeratorReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse completeWeightEnumeratorReceipt
