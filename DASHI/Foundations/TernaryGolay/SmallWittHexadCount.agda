module DASHI.Foundations.TernaryGolay.SmallWittHexadCount where

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
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Weight-six supports and the small Witt design.
--
-- The attachment's arithmetic 264 / 2 = 132 is necessary but not by itself
-- sufficient for the Steiner property: distinct sign-orbits could a priori
-- share a support. This module therefore computes the 132 distinct supports
-- and checks every one of the 792 pentads against them.
------------------------------------------------------------------------

infixr 6 _&&_

_&&_ : Bool → Bool → Bool
true && b = b
false && _ = false

_⇒_ : Bool → Bool → Bool
true ⇒ b = b
false ⇒ _ = true

boolEq : Bool → Bool → Bool
boolEq false false = true
boolEq true true = true
boolEq _ _ = false

nonzeroBool : TriTruth → Bool
nonzeroBool x with F3.triIsZero x
... | true = false
... | false = true

Support12 : Set
Support12 = Boundary.Vec12 Bool

supportOf : Boundary.Word12 → Support12
supportOf word =
  Boundary.vec12
    (nonzeroBool (Boundary.e0 word))
    (nonzeroBool (Boundary.e1 word))
    (nonzeroBool (Boundary.e2 word))
    (nonzeroBool (Boundary.e3 word))
    (nonzeroBool (Boundary.e4 word))
    (nonzeroBool (Boundary.e5 word))
    (nonzeroBool (Boundary.e6 word))
    (nonzeroBool (Boundary.e7 word))
    (nonzeroBool (Boundary.e8 word))
    (nonzeroBool (Boundary.e9 word))
    (nonzeroBool (Boundary.e10 word))
    (nonzeroBool (Boundary.e11 word))

supportEq : Support12 → Support12 → Bool
supportEq left right =
  boolEq (Boundary.e0 left) (Boundary.e0 right) &&
  boolEq (Boundary.e1 left) (Boundary.e1 right) &&
  boolEq (Boundary.e2 left) (Boundary.e2 right) &&
  boolEq (Boundary.e3 left) (Boundary.e3 right) &&
  boolEq (Boundary.e4 left) (Boundary.e4 right) &&
  boolEq (Boundary.e5 left) (Boundary.e5 right) &&
  boolEq (Boundary.e6 left) (Boundary.e6 right) &&
  boolEq (Boundary.e7 left) (Boundary.e7 right) &&
  boolEq (Boundary.e8 left) (Boundary.e8 right) &&
  boolEq (Boundary.e9 left) (Boundary.e9 right) &&
  boolEq (Boundary.e10 left) (Boundary.e10 right) &&
  boolEq (Boundary.e11 left) (Boundary.e11 right)

memberSupport : Support12 → List Support12 → Bool
memberSupport support [] = false
memberSupport support (candidate ∷ candidates) with supportEq support candidate
... | true = true
... | false = memberSupport support candidates

deduplicateSupports : List Support12 → List Support12
deduplicateSupports [] = []
deduplicateSupports (support ∷ supports) with memberSupport support supports
... | true = deduplicateSupports supports
... | false = support ∷ deduplicateSupports supports

boolContribution : Bool → Nat
boolContribution false = 0
boolContribution true = 1

supportWeight : Support12 → Nat
supportWeight support =
  boolContribution (Boundary.e0 support) +
  boolContribution (Boundary.e1 support) +
  boolContribution (Boundary.e2 support) +
  boolContribution (Boundary.e3 support) +
  boolContribution (Boundary.e4 support) +
  boolContribution (Boundary.e5 support) +
  boolContribution (Boundary.e6 support) +
  boolContribution (Boundary.e7 support) +
  boolContribution (Boundary.e8 support) +
  boolContribution (Boundary.e9 support) +
  boolContribution (Boundary.e10 support) +
  boolContribution (Boundary.e11 support)

weightSixCodewords : List Boundary.Word12
weightSixCodewords =
  Explicit.filter
    (λ word → Explicit.natEq (Explicit.hammingWeight word) 6)
    Explicit.allCodewords

weightSixCodewordCountIs264 :
  Explicit.listCount weightSixCodewords ≡ 264
weightSixCodewordCountIs264 = refl

weightSixSupports : List Support12
weightSixSupports = Explicit.map supportOf weightSixCodewords

hexadSupports : List Support12
hexadSupports = deduplicateSupports weightSixSupports

hexadSupportCountIs132 :
  Explicit.listCount hexadSupports ≡ 132
hexadSupportCountIs132 = refl

weightSixCodewordsAreTwoPerSupport :
  Explicit.listCount weightSixCodewords ≡ 2 * 132
weightSixCodewordsAreTwoPerSupport = refl

------------------------------------------------------------------------
-- Exhaustive S(5,6,12) check.
------------------------------------------------------------------------

allBits : List Bool
allBits = false ∷ true ∷ []

allSupports12 : List Support12
allSupports12 =
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
                                              Explicit.concatMap
                                                (λ b11 →
                                                  Boundary.vec12
                                                    b0 b1 b2 b3 b4 b5
                                                    b6 b7 b8 b9 b10 b11
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
        allBits)
    allBits

allSupports12CountIs4096 :
  Explicit.listCount allSupports12 ≡ 4096
allSupports12CountIs4096 = refl

pentads : List Support12
pentads =
  Explicit.filter
    (λ support → Explicit.natEq (supportWeight support) 5)
    allSupports12

pentadCountIs792 : Explicit.listCount pentads ≡ 792
pentadCountIs792 = refl

subsetSupport : Support12 → Support12 → Bool
subsetSupport small large =
  ((Boundary.e0 small) ⇒ (Boundary.e0 large)) &&
  ((Boundary.e1 small) ⇒ (Boundary.e1 large)) &&
  ((Boundary.e2 small) ⇒ (Boundary.e2 large)) &&
  ((Boundary.e3 small) ⇒ (Boundary.e3 large)) &&
  ((Boundary.e4 small) ⇒ (Boundary.e4 large)) &&
  ((Boundary.e5 small) ⇒ (Boundary.e5 large)) &&
  ((Boundary.e6 small) ⇒ (Boundary.e6 large)) &&
  ((Boundary.e7 small) ⇒ (Boundary.e7 large)) &&
  ((Boundary.e8 small) ⇒ (Boundary.e8 large)) &&
  ((Boundary.e9 small) ⇒ (Boundary.e9 large)) &&
  ((Boundary.e10 small) ⇒ (Boundary.e10 large)) &&
  ((Boundary.e11 small) ⇒ (Boundary.e11 large))

countContaining : Support12 → List Support12 → Nat
countContaining pentad [] = zero
countContaining pentad (hexad ∷ hexads) with subsetSupport pentad hexad
... | true = suc (countContaining pentad hexads)
... | false = countContaining pentad hexads

pentadHasUniqueHexad : Support12 → Bool
pentadHasUniqueHexad pentad =
  Explicit.natEq (countContaining pentad hexadSupports) 1

everyPentadHasUniqueHexadCheck : Bool
everyPentadHasUniqueHexadCheck =
  Explicit.allList pentadHasUniqueHexad pentads

everyPentadHasUniqueHexad :
  everyPentadHasUniqueHexadCheck ≡ true
everyPentadHasUniqueHexad = refl

hexadIncidenceArithmetic :
  132 + 132 + 132 + 132 + 132 + 132 ≡ 792
hexadIncidenceArithmetic = refl

record SmallWittFiniteCertificate : Set where
  constructor smallWittFiniteCertificate
  field
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String
    weightSixWords : Explicit.listCount weightSixCodewords ≡ 264
    distinctHexads : Explicit.listCount hexadSupports ≡ 132
    totalPentads : Explicit.listCount pentads ≡ 792
    everyPentadExactlyOneHexad : everyPentadHasUniqueHexadCheck ≡ true
    theoremImportSubstitutedForComputation : Bool
    theoremImportSubstitutedForComputationIsFalse :
      theoremImportSubstitutedForComputation ≡ false

canonicalSmallWittFiniteCertificate : SmallWittFiniteCertificate
canonicalSmallWittFiniteCertificate =
  smallWittFiniteCertificate
    (Sources.author Sources.plessGolayUniquenessEntry)
    (Sources.title Sources.plessGolayUniquenessEntry)
    "10.1016/0012-365X(92)90569-2"
    weightSixCodewordCountIs264
    hexadSupportCountIs132
    pentadCountIs792
    everyPentadHasUniqueHexad
    false refl

smallWittGenericReceipt : GenericReceipt.GenericReceipt
smallWittGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "small Witt S(5,6,12) finite certificate"
    "DASHI.Foundations.TernaryGolay.SmallWittHexadCount"
    "canonicalSmallWittFiniteCertificate"
    "the explicit ternary code has 264 weight-six words, 132 distinct supports, 792 pentads, and an exhaustive unique-containing-hexad check"
    "the cited uniqueness/design theorem calibrates the result but does not replace the kernel-reducible finite check"
    "agda -i . DASHI/Foundations/TernaryGolay/SmallWittHexadCount.agda"

smallWittGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim smallWittGenericReceipt ≡ false
smallWittGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse smallWittGenericReceipt
