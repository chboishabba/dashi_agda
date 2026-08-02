module DASHI.Foundations.TernaryGolay.ExplicitCode729 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_+_)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high )
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.TernaryGolay.CodeBoundary as Boundary
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Explicit [12,6,6]_3 presentation.
--
-- The six rows below are a systematic row-reduction (with one coordinate
-- permutation) of six independent rows of the order-12 Hadamard matrix in
-- Noam D. Elkies, "The ternary Golay codes and related structures".
-- Entries 0,1,2 are represented by tri-low, tri-mid, tri-high.
--
-- All 3^6 messages are enumerated below. The resulting kernel-normalised
-- computations provide exact codeword counts, weight distribution and Gram
-- zero receipts. Attribution is not a proof import; the finite calculations
-- are the local proof surface.
------------------------------------------------------------------------

infixr 5 _++_
infixr 6 _&&_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_&&_ : Bool → Bool → Bool
true && b = b
false && _ = false

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

filter : ∀ {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true = x ∷ filter p xs
... | false = filter p xs

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

allList : ∀ {A : Set} → (A → Bool) → List A → Bool
allList p [] = true
allList p (x ∷ xs) = p x && allList p xs

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc _) = false
natEq (suc _) zero = false
natEq (suc m) (suc n) = natEq m n

triEq : TriTruth → TriTruth → Bool
triEq tri-low tri-low = true
triEq tri-mid tri-mid = true
triEq tri-high tri-high = true
triEq _ _ = false

zeroF3 : TriTruth
zeroF3 = tri-low

oneF3 : TriTruth
oneF3 = tri-mid

twoF3 : TriTruth
twoF3 = tri-high

add6 :
  TriTruth → TriTruth → TriTruth →
  TriTruth → TriTruth → TriTruth →
  TriTruth
add6 a b c d e f =
  F3.triAdd a
    (F3.triAdd b
      (F3.triAdd c
        (F3.triAdd d
          (F3.triAdd e f))))

neg : TriTruth → TriTruth
neg = F3.triNeg

------------------------------------------------------------------------
-- Systematic generator matrix
--
-- [ I_6 | A ], where
--
-- A =
-- 2 0 2 1 1 2
-- 2 1 1 2 0 2
-- 2 2 0 2 1 1
-- 2 2 1 1 2 0
-- 2 1 2 0 2 1
-- 0 1 1 1 1 1
------------------------------------------------------------------------

encode : Boundary.Message6 → Boundary.Word12
encode m =
  Boundary.vec12
    a b c d e f
    (add6 (neg a) (neg b) (neg c) (neg d) (neg e) zeroF3)
    (add6 zeroF3 b (neg c) (neg d) e f)
    (add6 (neg a) b zeroF3 d (neg e) f)
    (add6 a (neg b) (neg c) d zeroF3 f)
    (add6 a zeroF3 c (neg d) (neg e) f)
    (add6 (neg a) (neg b) c zeroF3 e f)
  where
    a = Boundary.c0 m
    b = Boundary.c1 m
    c = Boundary.c2 m
    d = Boundary.c3 m
    e = Boundary.c4 m
    f = Boundary.c5 m

decodeSystematic : Boundary.Word12 → Boundary.Message6
decodeSystematic w =
  Boundary.vec6
    (Boundary.e0 w)
    (Boundary.e1 w)
    (Boundary.e2 w)
    (Boundary.e3 w)
    (Boundary.e4 w)
    (Boundary.e5 w)

decodeEncode :
  (m : Boundary.Message6) →
  decodeSystematic (encode m) ≡ m
decodeEncode (Boundary.vec6 a b c d e f) = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

cong :
  ∀ {A B : Set} (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
cong f refl = refl

encodeInjective :
  ∀ {left right : Boundary.Message6} →
  encode left ≡ encode right →
  left ≡ right
encodeInjective {left} {right} encodedEqual =
  trans
    (sym (decodeEncode left))
    (trans
      (cong decodeSystematic encodedEqual)
      (decodeEncode right))

------------------------------------------------------------------------
-- Complete 3^6 message carrier and exact codeword enumeration.
------------------------------------------------------------------------

allF3 : List TriTruth
allF3 = tri-low ∷ tri-mid ∷ tri-high ∷ []

allMessages : List Boundary.Message6
allMessages =
  concatMap
    (λ a →
      concatMap
        (λ b →
          concatMap
            (λ c →
              concatMap
                (λ d →
                  concatMap
                    (λ e →
                      concatMap
                        (λ f → Boundary.vec6 a b c d e f ∷ [])
                        allF3)
                    allF3)
                allF3)
            allF3)
        allF3)
    allF3

allMessagesCountIs729 : listCount allMessages ≡ 729
allMessagesCountIs729 = refl

allCodewords : List Boundary.Word12
allCodewords = map encode allMessages

allCodewordsEnumeratedCountIs729 : listCount allCodewords ≡ 729
allCodewordsEnumeratedCountIs729 = refl

nonzeroContribution : TriTruth → Nat
nonzeroContribution x with F3.triIsZero x
... | true = 0
... | false = 1

hammingWeight : Boundary.Word12 → Nat
hammingWeight w =
  nonzeroContribution (Boundary.e0 w) +
  nonzeroContribution (Boundary.e1 w) +
  nonzeroContribution (Boundary.e2 w) +
  nonzeroContribution (Boundary.e3 w) +
  nonzeroContribution (Boundary.e4 w) +
  nonzeroContribution (Boundary.e5 w) +
  nonzeroContribution (Boundary.e6 w) +
  nonzeroContribution (Boundary.e7 w) +
  nonzeroContribution (Boundary.e8 w) +
  nonzeroContribution (Boundary.e9 w) +
  nonzeroContribution (Boundary.e10 w) +
  nonzeroContribution (Boundary.e11 w)

countWeight : Nat → List Boundary.Word12 → Nat
countWeight target [] = zero
countWeight target (word ∷ words) with natEq target (hammingWeight word)
... | true = suc (countWeight target words)
... | false = countWeight target words

weight0Count : countWeight 0 allCodewords ≡ 1
weight0Count = refl

weight1Count : countWeight 1 allCodewords ≡ 0
weight1Count = refl

weight2Count : countWeight 2 allCodewords ≡ 0
weight2Count = refl

weight3Count : countWeight 3 allCodewords ≡ 0
weight3Count = refl

weight4Count : countWeight 4 allCodewords ≡ 0
weight4Count = refl

weight5Count : countWeight 5 allCodewords ≡ 0
weight5Count = refl

weight6Count : countWeight 6 allCodewords ≡ 264
weight6Count = refl

weight7Count : countWeight 7 allCodewords ≡ 0
weight7Count = refl

weight8Count : countWeight 8 allCodewords ≡ 0
weight8Count = refl

weight9Count : countWeight 9 allCodewords ≡ 440
weight9Count = refl

weight10Count : countWeight 10 allCodewords ≡ 0
weight10Count = refl

weight11Count : countWeight 11 allCodewords ≡ 0
weight11Count = refl

weight12Count : countWeight 12 allCodewords ≡ 24
weight12Count = refl

weightCoefficientSumIs729 :
  1 + 264 + 440 + 24 ≡ 729
weightCoefficientSumIs729 = refl

------------------------------------------------------------------------
-- Generator Gram matrix.
------------------------------------------------------------------------

basis0 basis1 basis2 basis3 basis4 basis5 : Boundary.Message6
basis0 = Boundary.vec6 oneF3 zeroF3 zeroF3 zeroF3 zeroF3 zeroF3
basis1 = Boundary.vec6 zeroF3 oneF3 zeroF3 zeroF3 zeroF3 zeroF3
basis2 = Boundary.vec6 zeroF3 zeroF3 oneF3 zeroF3 zeroF3 zeroF3
basis3 = Boundary.vec6 zeroF3 zeroF3 zeroF3 oneF3 zeroF3 zeroF3
basis4 = Boundary.vec6 zeroF3 zeroF3 zeroF3 zeroF3 oneF3 zeroF3
basis5 = Boundary.vec6 zeroF3 zeroF3 zeroF3 zeroF3 zeroF3 oneF3

generatorRows : List Boundary.Word12
generatorRows =
  encode basis0 ∷ encode basis1 ∷ encode basis2 ∷
  encode basis3 ∷ encode basis4 ∷ encode basis5 ∷ []

dot : Boundary.Word12 → Boundary.Word12 → TriTruth
dot left right =
  add6
    (add6
      (F3.triMul (Boundary.e0 left) (Boundary.e0 right))
      (F3.triMul (Boundary.e1 left) (Boundary.e1 right))
      (F3.triMul (Boundary.e2 left) (Boundary.e2 right))
      (F3.triMul (Boundary.e3 left) (Boundary.e3 right))
      (F3.triMul (Boundary.e4 left) (Boundary.e4 right))
      (F3.triMul (Boundary.e5 left) (Boundary.e5 right)))
    (add6
      (F3.triMul (Boundary.e6 left) (Boundary.e6 right))
      (F3.triMul (Boundary.e7 left) (Boundary.e7 right))
      (F3.triMul (Boundary.e8 left) (Boundary.e8 right))
      (F3.triMul (Boundary.e9 left) (Boundary.e9 right))
      (F3.triMul (Boundary.e10 left) (Boundary.e10 right))
      (F3.triMul (Boundary.e11 left) (Boundary.e11 right)))
    zeroF3 zeroF3 zeroF3 zeroF3

rowOrthogonalToAll :
  Boundary.Word12 → List Boundary.Word12 → Bool
rowOrthogonalToAll row [] = true
rowOrthogonalToAll row (other ∷ others) =
  triEq (dot row other) zeroF3 &&
  rowOrthogonalToAll row others

gramZeroCheck : List Boundary.Word12 → Bool
gramZeroCheck [] = true
gramZeroCheck (row ∷ rows) =
  rowOrthogonalToAll row generatorRows &&
  gramZeroCheck rows

generatorGramIsZero : gramZeroCheck generatorRows ≡ true
generatorGramIsZero = refl

record ExplicitTernaryGolayReceipt : Set where
  constructor explicitTernaryGolayReceipt
  field
    sourceAuthor : String
    sourceTitle : String
    sourceURL : String
    generatorRowsCount : listCount generatorRows ≡ 6
    messageCount : listCount allMessages ≡ 729
    systematicLeftInverse : (m : Boundary.Message6) →
      decodeSystematic (encode m) ≡ m
    gramZero : gramZeroCheck generatorRows ≡ true
    zeroCount : countWeight 0 allCodewords ≡ 1
    sixCount : countWeight 6 allCodewords ≡ 264
    nineCount : countWeight 9 allCodewords ≡ 440
    twelveCount : countWeight 12 allCodewords ≡ 24
    noWeightOne : countWeight 1 allCodewords ≡ 0
    noWeightTwo : countWeight 2 allCodewords ≡ 0
    noWeightThree : countWeight 3 allCodewords ≡ 0
    noWeightFour : countWeight 4 allCodewords ≡ 0
    noWeightFive : countWeight 5 allCodewords ≡ 0

canonicalExplicitTernaryGolayReceipt : ExplicitTernaryGolayReceipt
canonicalExplicitTernaryGolayReceipt =
  explicitTernaryGolayReceipt
    (Sources.author Sources.elkiesTernaryGolayEntry)
    (Sources.title Sources.elkiesTernaryGolayEntry)
    (Sources.canonicalURL Sources.elkiesTernaryGolayEntry)
    refl
    allMessagesCountIs729
    decodeEncode
    generatorGramIsZero
    weight0Count
    weight6Count
    weight9Count
    weight12Count
    weight1Count
    weight2Count
    weight3Count
    weight4Count
    weight5Count

explicitTernaryGolayGenericReceipt : GenericReceipt.GenericReceipt
explicitTernaryGolayGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "explicit ternary Golay 729-word construction"
    "DASHI.Foundations.TernaryGolay.ExplicitCode729"
    "canonicalExplicitTernaryGolayReceipt"
    "an explicit systematic generator, left inverse, six-by-six zero Gram receipt, 729-message enumeration, minimum weight six, and exact 1/264/440/24 weight distribution are kernel-reducible finite calculations"
    "the identification with the unique ternary Golay equivalence class is separately attributed; no coding-theory citation is silently treated as an Agda proof"
    "agda -i . DASHI/Foundations/TernaryGolay/ExplicitCode729.agda"

explicitTernaryGolayGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim explicitTernaryGolayGenericReceipt ≡ false
explicitTernaryGolayGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse explicitTernaryGolayGenericReceipt
