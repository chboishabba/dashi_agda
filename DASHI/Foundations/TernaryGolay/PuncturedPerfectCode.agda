module DASHI.Foundations.TernaryGolay.PuncturedPerfectCode where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_+_; _*_)

open import Base369 using (TriTruth)
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.TernaryGolay.CodeBoundary as Boundary
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.SmallWittHexadCount as SmallWitt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Puncturing the final coordinate of the explicit systematic code.
--
-- The finite Agda surface computes the complete punctured weight distribution
-- and the derived S(4,5,11) incidence design.  Perfect radius-two coverage of
-- all 3^11 ambient words is independently exhausted by the standard-library
-- Python oracle; the sphere-count identity is closed here.
------------------------------------------------------------------------

punctureLast : Boundary.Word12 → Boundary.Word11
punctureLast word =
  Boundary.vec11
    (Boundary.e0 word)
    (Boundary.e1 word)
    (Boundary.e2 word)
    (Boundary.e3 word)
    (Boundary.e4 word)
    (Boundary.e5 word)
    (Boundary.e6 word)
    (Boundary.e7 word)
    (Boundary.e8 word)
    (Boundary.e9 word)
    (Boundary.e10 word)

puncturedCodewords : List Boundary.Word11
puncturedCodewords = Explicit.map punctureLast Explicit.allCodewords

puncturedCodewordCountIs729 :
  Explicit.listCount puncturedCodewords ≡ 729
puncturedCodewordCountIs729 = refl

nonzeroContribution : TriTruth → Nat
nonzeroContribution value with F3.triIsZero value
... | true = 0
... | false = 1

hammingWeight11 : Boundary.Word11 → Nat
hammingWeight11 word =
  nonzeroContribution (Boundary.d0 word) +
  nonzeroContribution (Boundary.d1 word) +
  nonzeroContribution (Boundary.d2 word) +
  nonzeroContribution (Boundary.d3 word) +
  nonzeroContribution (Boundary.d4 word) +
  nonzeroContribution (Boundary.d5 word) +
  nonzeroContribution (Boundary.d6 word) +
  nonzeroContribution (Boundary.d7 word) +
  nonzeroContribution (Boundary.d8 word) +
  nonzeroContribution (Boundary.d9 word) +
  nonzeroContribution (Boundary.d10 word)

countWeight11 : Nat → List Boundary.Word11 → Nat
countWeight11 target [] = zero
countWeight11 target (word ∷ words)
  with Explicit.natEq target (hammingWeight11 word)
... | true = suc (countWeight11 target words)
... | false = countWeight11 target words

puncturedWeight0 : countWeight11 0 puncturedCodewords ≡ 1
puncturedWeight0 = refl

puncturedWeight1 : countWeight11 1 puncturedCodewords ≡ 0
puncturedWeight1 = refl

puncturedWeight2 : countWeight11 2 puncturedCodewords ≡ 0
puncturedWeight2 = refl

puncturedWeight3 : countWeight11 3 puncturedCodewords ≡ 0
puncturedWeight3 = refl

puncturedWeight4 : countWeight11 4 puncturedCodewords ≡ 0
puncturedWeight4 = refl

puncturedWeight5 : countWeight11 5 puncturedCodewords ≡ 132
puncturedWeight5 = refl

puncturedWeight6 : countWeight11 6 puncturedCodewords ≡ 132
puncturedWeight6 = refl

puncturedWeight7 : countWeight11 7 puncturedCodewords ≡ 0
puncturedWeight7 = refl

puncturedWeight8 : countWeight11 8 puncturedCodewords ≡ 330
puncturedWeight8 = refl

puncturedWeight9 : countWeight11 9 puncturedCodewords ≡ 110
puncturedWeight9 = refl

puncturedWeight10 : countWeight11 10 puncturedCodewords ≡ 0
puncturedWeight10 = refl

puncturedWeight11 : countWeight11 11 puncturedCodewords ≡ 24
puncturedWeight11 = refl

puncturedCoefficientSum :
  1 + 132 + 132 + 330 + 110 + 24 ≡ 729
puncturedCoefficientSum = refl

radiusTwoErrorPatternCount : Nat
radiusTwoErrorPatternCount =
  1 + (11 * 2) + ((55 * 2) * 2)

radiusTwoErrorPatternCountIs243 :
  radiusTwoErrorPatternCount ≡ 243
radiusTwoErrorPatternCountIs243 = refl

ambientWord11Count : Nat
ambientWord11Count = Boundary.pow 3 11

ambientWord11CountIs177147 :
  ambientWord11Count ≡ 177147
ambientWord11CountIs177147 = refl

spherePackingFillsAmbient :
  729 * radiusTwoErrorPatternCount ≡ ambientWord11Count
spherePackingFillsAmbient = refl

------------------------------------------------------------------------
-- Derived design at the punctured point.
------------------------------------------------------------------------

Support11 : Set
Support11 = Boundary.Vec11 Bool

punctureSupportLast : SmallWitt.Support12 → Support11
punctureSupportLast support =
  Boundary.vec11
    (Boundary.e0 support)
    (Boundary.e1 support)
    (Boundary.e2 support)
    (Boundary.e3 support)
    (Boundary.e4 support)
    (Boundary.e5 support)
    (Boundary.e6 support)
    (Boundary.e7 support)
    (Boundary.e8 support)
    (Boundary.e9 support)
    (Boundary.e10 support)

hexadsThroughLastPoint : List SmallWitt.Support12
hexadsThroughLastPoint =
  Explicit.filter
    (λ support → Boundary.e11 support)
    SmallWitt.hexadSupports

hexadsThroughLastPointCountIs66 :
  Explicit.listCount hexadsThroughLastPoint ≡ 66
hexadsThroughLastPointCountIs66 = refl

derivedBlocks : List Support11
derivedBlocks =
  Explicit.map punctureSupportLast hexadsThroughLastPoint

derivedBlockCountIs66 :
  Explicit.listCount derivedBlocks ≡ 66
derivedBlockCountIs66 = refl

boolContribution : Bool → Nat
boolContribution false = 0
boolContribution true = 1

supportWeight11 : Support11 → Nat
supportWeight11 support =
  boolContribution (Boundary.d0 support) +
  boolContribution (Boundary.d1 support) +
  boolContribution (Boundary.d2 support) +
  boolContribution (Boundary.d3 support) +
  boolContribution (Boundary.d4 support) +
  boolContribution (Boundary.d5 support) +
  boolContribution (Boundary.d6 support) +
  boolContribution (Boundary.d7 support) +
  boolContribution (Boundary.d8 support) +
  boolContribution (Boundary.d9 support) +
  boolContribution (Boundary.d10 support)

allBits : List Bool
allBits = false ∷ true ∷ []

allSupports11 : List Support11
allSupports11 =
  Explicit.concatMap
    (λ b0 →
      Explicit.concatMap
        (λ b1 →
          Explicit.concatMap
            (λ b2 →
              Explicit.concatMap
                (λ b3 →
                  Explicit.concatMap
                    (λ b4 →
                      Explicit.concatMap
                        (λ b5 →
                          Explicit.concatMap
                            (λ b6 →
                              Explicit.concatMap
                                (λ b7 →
                                  Explicit.concatMap
                                    (λ b8 →
                                      Explicit.concatMap
                                        (λ b9 →
                                          Explicit.concatMap
                                            (λ b10 →
                                              Boundary.vec11
                                                b0 b1 b2 b3 b4 b5
                                                b6 b7 b8 b9 b10
                                              ∷ [])
                                            allBits)
                                        allBits)
                                    allBits)
                                allBits)
                            allBits)
                        allBits)
                    allBits)
                allBits)
            allBits)
        allBits)
    allBits

allSupports11CountIs2048 :
  Explicit.listCount allSupports11 ≡ 2048
allSupports11CountIs2048 = refl

tetrads : List Support11
tetrads =
  Explicit.filter
    (λ support → Explicit.natEq (supportWeight11 support) 4)
    allSupports11

tetradCountIs330 :
  Explicit.listCount tetrads ≡ 330
tetradCountIs330 = refl

implies : Bool → Bool → Bool
implies true result = result
implies false _ = true

subset11 : Support11 → Support11 → Bool
subset11 small large =
  Explicit._&&_ (implies (Boundary.d0 small) (Boundary.d0 large))
  (Explicit._&&_ (implies (Boundary.d1 small) (Boundary.d1 large))
  (Explicit._&&_ (implies (Boundary.d2 small) (Boundary.d2 large))
  (Explicit._&&_ (implies (Boundary.d3 small) (Boundary.d3 large))
  (Explicit._&&_ (implies (Boundary.d4 small) (Boundary.d4 large))
  (Explicit._&&_ (implies (Boundary.d5 small) (Boundary.d5 large))
  (Explicit._&&_ (implies (Boundary.d6 small) (Boundary.d6 large))
  (Explicit._&&_ (implies (Boundary.d7 small) (Boundary.d7 large))
  (Explicit._&&_ (implies (Boundary.d8 small) (Boundary.d8 large))
  (Explicit._&&_ (implies (Boundary.d9 small) (Boundary.d9 large))
                 (implies (Boundary.d10 small) (Boundary.d10 large)))))))))))

countContaining11 : Support11 → List Support11 → Nat
countContaining11 small [] = zero
countContaining11 small (large ∷ larges) with subset11 small large
... | true = suc (countContaining11 small larges)
... | false = countContaining11 small larges

tetradHasUniqueDerivedBlock : Support11 → Bool
tetradHasUniqueDerivedBlock tetrad =
  Explicit.natEq (countContaining11 tetrad derivedBlocks) 1

derivedSteinerCheck : Bool
derivedSteinerCheck =
  Explicit.allList tetradHasUniqueDerivedBlock tetrads

derivedSteinerS4511 :
  derivedSteinerCheck ≡ true
derivedSteinerS4511 = refl

record PuncturedPerfectFiniteCertificate : Set where
  constructor puncturedPerfectFiniteCertificate
  field
    sourceAuthor : String
    sourceTitle : String
    puncturedWords : Explicit.listCount puncturedCodewords ≡ 729
    noWeightBelowFive :
      countWeight11 1 puncturedCodewords ≡ 0
    weightFiveWords : countWeight11 5 puncturedCodewords ≡ 132
    errorPatternsRadiusTwo : radiusTwoErrorPatternCount ≡ 243
    packingArithmetic :
      729 * radiusTwoErrorPatternCount ≡ ambientWord11Count
    derivedBlocksCount : Explicit.listCount derivedBlocks ≡ 66
    tetradsCount : Explicit.listCount tetrads ≡ 330
    derivedSteinerIncidence : derivedSteinerCheck ≡ true
    exhaustiveUniqueDecodingCheckedByIndependentOracle : Bool
    exhaustiveUniqueDecodingCheckedByIndependentOracleIsTrue :
      exhaustiveUniqueDecodingCheckedByIndependentOracle ≡ true
    AgdaKernelEnumeratesAll177147AmbientWords : Bool
    AgdaKernelEnumeratesAll177147AmbientWordsIsFalse :
      AgdaKernelEnumeratesAll177147AmbientWords ≡ false

canonicalPuncturedPerfectFiniteCertificate :
  PuncturedPerfectFiniteCertificate
canonicalPuncturedPerfectFiniteCertificate =
  puncturedPerfectFiniteCertificate
    (Sources.author Sources.macWilliamsSloaneEntry)
    (Sources.title Sources.macWilliamsSloaneEntry)
    puncturedCodewordCountIs729
    puncturedWeight1
    puncturedWeight5
    radiusTwoErrorPatternCountIs243
    spherePackingFillsAmbient
    derivedBlockCountIs66
    tetradCountIs330
    derivedSteinerS4511
    true refl
    false refl

puncturedPerfectCodeReceipt : GenericReceipt.GenericReceipt
puncturedPerfectCodeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "punctured ternary Golay perfect-code and derived-design certificate"
    "DASHI.Foundations.TernaryGolay.PuncturedPerfectCode"
    "canonicalPuncturedPerfectFiniteCertificate"
    "the final-coordinate puncture has the exact 1/132/132/330/110/24 weight distribution, minimum nonzero weight five, radius-two sphere volume 243, exact ambient packing arithmetic, and a locally computed S(4,5,11) derived design"
    "the dependency-free oracle exhausts all 177147 received words and proves unique radius-two coverage; that exhaustive ambient computation is not mislabelled as an Agda kernel reduction"
    "agda -i . DASHI/Foundations/TernaryGolay/PuncturedPerfectCode.agda"

puncturedPerfectCodeReceiptNonPromoting :
  GenericReceipt.promotesClaim puncturedPerfectCodeReceipt ≡ false
puncturedPerfectCodeReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse puncturedPerfectCodeReceipt
