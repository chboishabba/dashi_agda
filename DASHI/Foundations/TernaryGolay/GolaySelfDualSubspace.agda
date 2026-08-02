module DASHI.Foundations.TernaryGolay.GolaySelfDualSubspace where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high )
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.FiniteLinear.F3Subspace as Linear
import DASHI.Foundations.TernaryGolay.CodeBoundary as Boundary
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources

------------------------------------------------------------------------
-- Concrete first-class self-duality for the explicit ternary Golay code.
--
-- The proof uses three small reusable ideas:
--
-- * the code is represented by its actual image predicate;
-- * the dual is the standard coordinate-dot orthogonal complement;
-- * 729-message reflection checks the two presentation identities:
--     (1) the systematic encoder equals the generator-row linear combination;
--     (2) the systematic dual normal form is again an encoded codeword.
--
-- No uniqueness theorem is used to infer self-duality.
------------------------------------------------------------------------

infixr 6 _&&_
infix 4 _∈_

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

andTrueLeft : ∀ {a b} → a && b ≡ true → a ≡ true
andTrueLeft {true} {true} refl = refl
andTrueLeft {true} {false} ()
andTrueLeft {false} {true} ()
andTrueLeft {false} {false} ()

andTrueRight : ∀ {a b} → a && b ≡ true → b ≡ true
andTrueRight {true} {true} refl = refl
andTrueRight {true} {false} ()
andTrueRight {false} {true} ()
andTrueRight {false} {false} ()

allList : ∀ {A : Set} → (A → Bool) → List A → Bool
allList p [] = true
allList p (x ∷ xs) = p x && allList p xs

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

appendLeft :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ xs → x ∈ (Explicit._++_ xs ys)
appendLeft here = here
appendLeft (there membership) = there (appendLeft membership)

appendRight :
  ∀ {A : Set} {x : A} {xs ys : List A} →
  x ∈ ys → x ∈ (Explicit._++_ xs ys)
appendRight {xs = []} membership = membership
appendRight {xs = y ∷ xs} membership =
  there (appendRight {xs = xs} membership)

concatMapMember :
  ∀ {A B : Set}
    {f : A → List B}
    {a : A} {b : B} {xs : List A} →
  a ∈ xs →
  b ∈ f a →
  b ∈ Explicit.concatMap f xs
concatMapMember here outputMember = appendLeft outputMember
concatMapMember (there inputMember) outputMember =
  appendRight (concatMapMember inputMember outputMember)

allListMember :
  ∀ {A : Set} {p : A → Bool} {x : A} {xs : List A} →
  x ∈ xs →
  allList p xs ≡ true →
  p x ≡ true
allListMember here allTrue = andTrueLeft allTrue
allListMember (there membership) allTrue =
  allListMember membership (andTrueRight allTrue)

allF3Complete : (x : TriTruth) → x ∈ Explicit.allF3
allF3Complete tri-low = here
allF3Complete tri-mid = there here
allF3Complete tri-high = there (there here)

allMessagesComplete :
  (message : Boundary.Message6) →
  message ∈ Explicit.allMessages
allMessagesComplete (Boundary.vec6 x0 x1 x2 x3 x4 x5) =
  concatMapMember (allF3Complete x0)
    (concatMapMember (allF3Complete x1)
      (concatMapMember (allF3Complete x2)
        (concatMapMember (allF3Complete x3)
          (concatMapMember (allF3Complete x4)
            (concatMapMember (allF3Complete x5) here)))))

triEqSound :
  (x y : TriTruth) →
  Explicit.triEq x y ≡ true →
  x ≡ y
triEqSound tri-low tri-low refl = refl
triEqSound tri-low tri-mid ()
triEqSound tri-low tri-high ()
triEqSound tri-mid tri-low ()
triEqSound tri-mid tri-mid refl = refl
triEqSound tri-mid tri-high ()
triEqSound tri-high tri-low ()
triEqSound tri-high tri-mid ()
triEqSound tri-high tri-high refl = refl

messageExt :
  ∀ {left right : Boundary.Message6} →
  Boundary.c0 left ≡ Boundary.c0 right →
  Boundary.c1 left ≡ Boundary.c1 right →
  Boundary.c2 left ≡ Boundary.c2 right →
  Boundary.c3 left ≡ Boundary.c3 right →
  Boundary.c4 left ≡ Boundary.c4 right →
  Boundary.c5 left ≡ Boundary.c5 right →
  left ≡ right
messageExt
  {Boundary.vec6 x0 x1 x2 x3 x4 x5}
  {Boundary.vec6 y0 y1 y2 y3 y4 y5}
  refl refl refl refl refl refl = refl

wordExt :
  ∀ {left right : Boundary.Word12} →
  Boundary.e0 left ≡ Boundary.e0 right →
  Boundary.e1 left ≡ Boundary.e1 right →
  Boundary.e2 left ≡ Boundary.e2 right →
  Boundary.e3 left ≡ Boundary.e3 right →
  Boundary.e4 left ≡ Boundary.e4 right →
  Boundary.e5 left ≡ Boundary.e5 right →
  Boundary.e6 left ≡ Boundary.e6 right →
  Boundary.e7 left ≡ Boundary.e7 right →
  Boundary.e8 left ≡ Boundary.e8 right →
  Boundary.e9 left ≡ Boundary.e9 right →
  Boundary.e10 left ≡ Boundary.e10 right →
  Boundary.e11 left ≡ Boundary.e11 right →
  left ≡ right
wordExt
  {Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11}
  {Boundary.vec12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11}
  refl refl refl refl refl refl
  refl refl refl refl refl refl = refl

messageEq : Boundary.Message6 → Boundary.Message6 → Bool
messageEq left right =
  Explicit.triEq (Boundary.c0 left) (Boundary.c0 right) &&
  Explicit.triEq (Boundary.c1 left) (Boundary.c1 right) &&
  Explicit.triEq (Boundary.c2 left) (Boundary.c2 right) &&
  Explicit.triEq (Boundary.c3 left) (Boundary.c3 right) &&
  Explicit.triEq (Boundary.c4 left) (Boundary.c4 right) &&
  Explicit.triEq (Boundary.c5 left) (Boundary.c5 right)

messageEqSound :
  ∀ {left right} →
  messageEq left right ≡ true →
  left ≡ right
messageEqSound {left} {right} equality =
  messageExt
    (triEqSound _ _ (andTrueLeft equality))
    (triEqSound _ _ (andTrueLeft (andTrueRight equality)))
    (triEqSound _ _
      (andTrueLeft (andTrueRight (andTrueRight equality))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight (andTrueRight (andTrueRight equality)))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight (andTrueRight (andTrueRight equality))))))
    (triEqSound _ _
      (andTrueRight
        (andTrueRight
          (andTrueRight (andTrueRight (andTrueRight equality))))))

wordEq : Boundary.Word12 → Boundary.Word12 → Bool
wordEq left right =
  Explicit.triEq (Boundary.e0 left) (Boundary.e0 right) &&
  Explicit.triEq (Boundary.e1 left) (Boundary.e1 right) &&
  Explicit.triEq (Boundary.e2 left) (Boundary.e2 right) &&
  Explicit.triEq (Boundary.e3 left) (Boundary.e3 right) &&
  Explicit.triEq (Boundary.e4 left) (Boundary.e4 right) &&
  Explicit.triEq (Boundary.e5 left) (Boundary.e5 right) &&
  Explicit.triEq (Boundary.e6 left) (Boundary.e6 right) &&
  Explicit.triEq (Boundary.e7 left) (Boundary.e7 right) &&
  Explicit.triEq (Boundary.e8 left) (Boundary.e8 right) &&
  Explicit.triEq (Boundary.e9 left) (Boundary.e9 right) &&
  Explicit.triEq (Boundary.e10 left) (Boundary.e10 right) &&
  Explicit.triEq (Boundary.e11 left) (Boundary.e11 right)

wordEqSound :
  ∀ {left right} →
  wordEq left right ≡ true →
  left ≡ right
wordEqSound {left} {right} equality =
  wordExt
    (triEqSound _ _ (andTrueLeft equality))
    (triEqSound _ _ (andTrueLeft (andTrueRight equality)))
    (triEqSound _ _
      (andTrueLeft (andTrueRight (andTrueRight equality))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight (andTrueRight (andTrueRight equality)))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight (andTrueRight (andTrueRight equality))))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight
            (andTrueRight (andTrueRight (andTrueRight equality)))))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight
            (andTrueRight
              (andTrueRight (andTrueRight (andTrueRight equality))))))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight
            (andTrueRight
              (andTrueRight
                (andTrueRight (andTrueRight (andTrueRight equality)))))))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight
            (andTrueRight
              (andTrueRight
                (andTrueRight
                  (andTrueRight (andTrueRight (andTrueRight equality))))))))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight
            (andTrueRight
              (andTrueRight
                (andTrueRight
                  (andTrueRight
                    (andTrueRight (andTrueRight (andTrueRight equality)))))))))))
    (triEqSound _ _
      (andTrueLeft
        (andTrueRight
          (andTrueRight
            (andTrueRight
              (andTrueRight
                (andTrueRight
                  (andTrueRight
                    (andTrueRight
                      (andTrueRight (andTrueRight (andTrueRight equality))))))))))))
    (triEqSound _ _
      (andTrueRight
        (andTrueRight
          (andTrueRight
            (andTrueRight
              (andTrueRight
                (andTrueRight
                  (andTrueRight
                    (andTrueRight
                      (andTrueRight (andTrueRight (andTrueRight equality))))))))))))

------------------------------------------------------------------------
-- Concrete F3 spaces on the existing message and word records.
------------------------------------------------------------------------

zeroMessage : Boundary.Message6
zeroMessage =
  Boundary.vec6
    F3.triZero F3.triZero F3.triZero
    F3.triZero F3.triZero F3.triZero

addMessage :
  Boundary.Message6 → Boundary.Message6 → Boundary.Message6
addMessage left right =
  Boundary.vec6
    (F3.triAdd (Boundary.c0 left) (Boundary.c0 right))
    (F3.triAdd (Boundary.c1 left) (Boundary.c1 right))
    (F3.triAdd (Boundary.c2 left) (Boundary.c2 right))
    (F3.triAdd (Boundary.c3 left) (Boundary.c3 right))
    (F3.triAdd (Boundary.c4 left) (Boundary.c4 right))
    (F3.triAdd (Boundary.c5 left) (Boundary.c5 right))

scaleMessage : TriTruth → Boundary.Message6 → Boundary.Message6
scaleMessage a message =
  Boundary.vec6
    (F3.triMul a (Boundary.c0 message))
    (F3.triMul a (Boundary.c1 message))
    (F3.triMul a (Boundary.c2 message))
    (F3.triMul a (Boundary.c3 message))
    (F3.triMul a (Boundary.c4 message))
    (F3.triMul a (Boundary.c5 message))

scaleMessageZero : (a : TriTruth) → scaleMessage a zeroMessage ≡ zeroMessage
scaleMessageZero tri-low = refl
scaleMessageZero tri-mid = refl
scaleMessageZero tri-high = refl

messageSpace : Linear.F3Space
messageSpace = record
  { Carrier = Boundary.Message6
  ; zero = zeroMessage
  ; add = addMessage
  ; scale = scaleMessage
  ; addZeroZero = refl
  ; scaleZero = scaleMessageZero
  }

zeroWord : Boundary.Word12
zeroWord =
  Boundary.vec12
    F3.triZero F3.triZero F3.triZero
    F3.triZero F3.triZero F3.triZero
    F3.triZero F3.triZero F3.triZero
    F3.triZero F3.triZero F3.triZero

addWord : Boundary.Word12 → Boundary.Word12 → Boundary.Word12
addWord left right =
  Boundary.vec12
    (F3.triAdd (Boundary.e0 left) (Boundary.e0 right))
    (F3.triAdd (Boundary.e1 left) (Boundary.e1 right))
    (F3.triAdd (Boundary.e2 left) (Boundary.e2 right))
    (F3.triAdd (Boundary.e3 left) (Boundary.e3 right))
    (F3.triAdd (Boundary.e4 left) (Boundary.e4 right))
    (F3.triAdd (Boundary.e5 left) (Boundary.e5 right))
    (F3.triAdd (Boundary.e6 left) (Boundary.e6 right))
    (F3.triAdd (Boundary.e7 left) (Boundary.e7 right))
    (F3.triAdd (Boundary.e8 left) (Boundary.e8 right))
    (F3.triAdd (Boundary.e9 left) (Boundary.e9 right))
    (F3.triAdd (Boundary.e10 left) (Boundary.e10 right))
    (F3.triAdd (Boundary.e11 left) (Boundary.e11 right))

scaleWord : TriTruth → Boundary.Word12 → Boundary.Word12
scaleWord a word =
  Boundary.vec12
    (F3.triMul a (Boundary.e0 word))
    (F3.triMul a (Boundary.e1 word))
    (F3.triMul a (Boundary.e2 word))
    (F3.triMul a (Boundary.e3 word))
    (F3.triMul a (Boundary.e4 word))
    (F3.triMul a (Boundary.e5 word))
    (F3.triMul a (Boundary.e6 word))
    (F3.triMul a (Boundary.e7 word))
    (F3.triMul a (Boundary.e8 word))
    (F3.triMul a (Boundary.e9 word))
    (F3.triMul a (Boundary.e10 word))
    (F3.triMul a (Boundary.e11 word))

scaleWordZero : (a : TriTruth) → scaleWord a zeroWord ≡ zeroWord
scaleWordZero tri-low = refl
scaleWordZero tri-mid = refl
scaleWordZero tri-high = refl

wordSpace : Linear.F3Space
wordSpace = record
  { Carrier = Boundary.Word12
  ; zero = zeroWord
  ; add = addWord
  ; scale = scaleWord
  ; addZeroZero = refl
  ; scaleZero = scaleWordZero
  }

messageValues : Boundary.Message6 → List TriTruth
messageValues message =
  Boundary.c0 message ∷ Boundary.c1 message ∷
  Boundary.c2 message ∷ Boundary.c3 message ∷
  Boundary.c4 message ∷ Boundary.c5 message ∷ []

headValues : Boundary.Word12 → List TriTruth
headValues word =
  Boundary.e0 word ∷ Boundary.e1 word ∷
  Boundary.e2 word ∷ Boundary.e3 word ∷
  Boundary.e4 word ∷ Boundary.e5 word ∷ []

tailValues : Boundary.Word12 → List TriTruth
tailValues word =
  Boundary.e6 word ∷ Boundary.e7 word ∷
  Boundary.e8 word ∷ Boundary.e9 word ∷
  Boundary.e10 word ∷ Boundary.e11 word ∷ []

headValuesAdd :
  (left right : Boundary.Word12) →
  headValues (addWord left right)
  ≡ Linear.zipAdd (headValues left) (headValues right)
headValuesAdd
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
  (Boundary.vec12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11) = refl

tailValuesAdd :
  (left right : Boundary.Word12) →
  tailValues (addWord left right)
  ≡ Linear.zipAdd (tailValues left) (tailValues right)
tailValuesAdd
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
  (Boundary.vec12 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11) = refl

headValuesScale :
  (a : TriTruth) (word : Boundary.Word12) →
  headValues (scaleWord a word)
  ≡ Linear.scaleList a (headValues word)
headValuesScale a
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = refl

tailValuesScale :
  (a : TriTruth) (word : Boundary.Word12) →
  tailValues (scaleWord a word)
  ≡ Linear.scaleList a (tailValues word)
tailValuesScale a
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = refl

wordDot : Boundary.Word12 → Boundary.Word12 → TriTruth
wordDot left right =
  F3.triAdd
    (Linear.dotList (headValues left) (headValues right))
    (Linear.dotList (tailValues left) (tailValues right))

wordDotAddLeft :
  (left₁ left₂ right : Boundary.Word12) →
  wordDot (addWord left₁ left₂) right
  ≡ F3.triAdd (wordDot left₁ right) (wordDot left₂ right)
wordDotAddLeft left₁ left₂ right =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (Linear.trans
        (Linear.cong
          (λ values → Linear.dotList values (headValues right))
          (headValuesAdd left₁ left₂))
        (Linear.dotAddLeft
          (headValues left₁) (headValues left₂) (headValues right)))
      (Linear.trans
        (Linear.cong
          (λ values → Linear.dotList values (tailValues right))
          (tailValuesAdd left₁ left₂))
        (Linear.dotAddLeft
          (tailValues left₁) (tailValues left₂) (tailValues right))))
    (Linear.addInterchange
      (Linear.dotList (headValues left₁) (headValues right))
      (Linear.dotList (headValues left₂) (headValues right))
      (Linear.dotList (tailValues left₁) (tailValues right))
      (Linear.dotList (tailValues left₂) (tailValues right)))

wordDotAddRight :
  (left right₁ right₂ : Boundary.Word12) →
  wordDot left (addWord right₁ right₂)
  ≡ F3.triAdd (wordDot left right₁) (wordDot left right₂)
wordDotAddRight left right₁ right₂ =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (Linear.trans
        (Linear.cong
          (Linear.dotList (headValues left))
          (headValuesAdd right₁ right₂))
        (Linear.dotAddRight
          (headValues left) (headValues right₁) (headValues right₂)))
      (Linear.trans
        (Linear.cong
          (Linear.dotList (tailValues left))
          (tailValuesAdd right₁ right₂))
        (Linear.dotAddRight
          (tailValues left) (tailValues right₁) (tailValues right₂))))
    (Linear.addInterchange
      (Linear.dotList (headValues left) (headValues right₁))
      (Linear.dotList (headValues left) (headValues right₂))
      (Linear.dotList (tailValues left) (tailValues right₁))
      (Linear.dotList (tailValues left) (tailValues right₂)))

wordDotScaleLeft :
  (a : TriTruth) (left right : Boundary.Word12) →
  wordDot (scaleWord a left) right
  ≡ F3.triMul a (wordDot left right)
wordDotScaleLeft a left right =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (Linear.trans
        (Linear.cong
          (λ values → Linear.dotList values (headValues right))
          (headValuesScale a left))
        (Linear.dotScaleLeft a (headValues left) (headValues right)))
      (Linear.trans
        (Linear.cong
          (λ values → Linear.dotList values (tailValues right))
          (tailValuesScale a left))
        (Linear.dotScaleLeft a (tailValues left) (tailValues right))))
    (Linear.sym
      (F3.triDistribˡ
        a
        (Linear.dotList (headValues left) (headValues right))
        (Linear.dotList (tailValues left) (tailValues right))))

wordDotScaleRight :
  (a : TriTruth) (left right : Boundary.Word12) →
  wordDot left (scaleWord a right)
  ≡ F3.triMul a (wordDot left right)
wordDotScaleRight a left right =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (Linear.trans
        (Linear.cong
          (Linear.dotList (headValues left))
          (headValuesScale a right))
        (Linear.dotScaleRight a (headValues left) (headValues right)))
      (Linear.trans
        (Linear.cong
          (Linear.dotList (tailValues left))
          (tailValuesScale a right))
        (Linear.dotScaleRight a (tailValues left) (tailValues right))))
    (Linear.sym
      (F3.triDistribˡ
        a
        (Linear.dotList (headValues left) (headValues right))
        (Linear.dotList (tailValues left) (tailValues right))))

wordDotZeroLeft :
  (right : Boundary.Word12) →
  wordDot zeroWord right ≡ F3.triZero
wordDotZeroLeft right = refl

wordDotZeroRight :
  (left : Boundary.Word12) →
  wordDot left zeroWord ≡ F3.triZero
wordDotZeroRight left =
  Linear.trans
    (Linear.sym
      (Linear.cong
        (wordDot left)
        (scaleWordZero tri-low)))
    (Linear.trans
      (wordDotScaleRight tri-low left zeroWord)
      refl)

------------------------------------------------------------------------
-- Generator-row linear combinations and finite reflection.
------------------------------------------------------------------------

linearCombination :
  List TriTruth → List Boundary.Word12 → Boundary.Word12
linearCombination [] rows = zeroWord
linearCombination coefficients [] = zeroWord
linearCombination (a ∷ as) (row ∷ rows) =
  addWord (scaleWord a row) (linearCombination as rows)

spanEncode : Boundary.Message6 → Boundary.Word12
spanEncode message =
  linearCombination (messageValues message) Explicit.generatorRows

spanEncodeCheck : Bool
spanEncodeCheck =
  allList
    (λ message → wordEq (spanEncode message) (Explicit.encode message))
    Explicit.allMessages

spanEncodeCheckIsTrue : spanEncodeCheck ≡ true
spanEncodeCheckIsTrue = refl

spanEncodeCorrect :
  (message : Boundary.Message6) →
  spanEncode message ≡ Explicit.encode message
spanEncodeCorrect message =
  wordEqSound
    (allListMember
      (allMessagesComplete message)
      spanEncodeCheckIsTrue)

rowOrthogonalBool :
  Boundary.Word12 → List Boundary.Word12 → Bool
rowOrthogonalBool word [] = true
rowOrthogonalBool word (row ∷ rows) =
  Explicit.triEq (wordDot word row) F3.triZero &&
  rowOrthogonalBool word rows

data AllDotsZero
    (word : Boundary.Word12) :
    List Boundary.Word12 → Set where
  allDotsNil : AllDotsZero word []
  allDotsCons :
    ∀ {row rows} →
    wordDot word row ≡ F3.triZero →
    AllDotsZero word rows →
    AllDotsZero word (row ∷ rows)

rowOrthogonalBoolSound :
  ∀ {word rows} →
  rowOrthogonalBool word rows ≡ true →
  AllDotsZero word rows
rowOrthogonalBoolSound {word} {[]} equality = allDotsNil
rowOrthogonalBoolSound {word} {row ∷ rows} equality =
  allDotsCons
    (triEqSound _ _ (andTrueLeft equality))
    (rowOrthogonalBoolSound (andTrueRight equality))

allEncodedWordsOrthogonalToRowsCheck : Bool
allEncodedWordsOrthogonalToRowsCheck =
  allList
    (λ message →
      rowOrthogonalBool
        (Explicit.encode message)
        Explicit.generatorRows)
    Explicit.allMessages

allEncodedWordsOrthogonalToRows :
  allEncodedWordsOrthogonalToRowsCheck ≡ true
allEncodedWordsOrthogonalToRows = refl

encodedWordOrthogonalToRows :
  (message : Boundary.Message6) →
  AllDotsZero (Explicit.encode message) Explicit.generatorRows
encodedWordOrthogonalToRows message =
  rowOrthogonalBoolSound
    (allListMember
      (allMessagesComplete message)
      allEncodedWordsOrthogonalToRows)

dotLinearCombinationZero :
  (word : Boundary.Word12) →
  (coefficients : List TriTruth) →
  (rows : List Boundary.Word12) →
  AllDotsZero word rows →
  wordDot word (linearCombination coefficients rows)
  ≡ F3.triZero
dotLinearCombinationZero word [] rows allZero =
  wordDotZeroRight word
dotLinearCombinationZero word (a ∷ as) [] allDotsNil =
  wordDotZeroRight word
dotLinearCombinationZero
  word (a ∷ as) (row ∷ rows)
  (allDotsCons rowZero remainingZero) =
  Linear.trans
    (wordDotAddRight
      word
      (scaleWord a row)
      (linearCombination as rows))
    (Linear.trans
      (Linear.cong₂ F3.triAdd
        (Linear.trans
          (wordDotScaleRight a word row)
          (Linear.trans
            (Linear.cong (F3.triMul a) rowZero)
            (F3.triMul-zeroʳ a)))
        (dotLinearCombinationZero
          word as rows remainingZero))
      refl)

------------------------------------------------------------------------
-- Code image and full coordinate-dot dual predicate.
------------------------------------------------------------------------

record CodeMember (word : Boundary.Word12) : Set where
  constructor codeMember
  field
    message : Boundary.Message6
    encoded : Explicit.encode message ≡ word

open CodeMember public

CodeDualMember : Boundary.Word12 → Set
CodeDualMember word =
  ∀ {codeword} →
  CodeMember codeword →
  wordDot word codeword ≡ F3.triZero

codeToDual :
  ∀ {word} →
  CodeMember word →
  CodeDualMember word
codeToDual (codeMember message refl)
  (codeMember otherMessage refl) =
  Linear.trans
    (Linear.cong
      (wordDot (Explicit.encode message))
      (Linear.sym (spanEncodeCorrect otherMessage)))
    (dotLinearCombinationZero
      (Explicit.encode message)
      (messageValues otherMessage)
      Explicit.generatorRows
      (encodedWordOrthogonalToRows message))

dualSubspace : Linear.F3Subspace wordSpace
dualSubspace = record
  { Member = CodeDualMember
  ; zeroMember = λ {codeword} codewordMember →
      wordDotZeroLeft codeword
  ; addMember = λ {left} {right} leftDual rightDual
      {codeword} codewordMember →
      Linear.trans
        (wordDotAddLeft left right codeword)
        (Linear.trans
          (Linear.cong₂ F3.triAdd
            (leftDual codewordMember)
            (rightDual codewordMember))
          refl)
  ; scaleMember = λ a {word} wordDual
      {codeword} codewordMember →
      Linear.trans
        (wordDotScaleLeft a word codeword)
        (Linear.trans
          (Linear.cong (F3.triMul a)
            (wordDual codewordMember))
          (F3.triMul-zeroʳ a))
  }

------------------------------------------------------------------------
-- Systematic normal form for every dual word.
------------------------------------------------------------------------

headOnly : Boundary.Word12 → Boundary.Word12
headOnly word =
  Boundary.vec12
    (Boundary.e0 word) (Boundary.e1 word)
    (Boundary.e2 word) (Boundary.e3 word)
    (Boundary.e4 word) (Boundary.e5 word)
    F3.triZero F3.triZero F3.triZero
    F3.triZero F3.triZero F3.triZero

tailOnly : Boundary.Word12 → Boundary.Word12
tailOnly word =
  Boundary.vec12
    F3.triZero F3.triZero F3.triZero
    F3.triZero F3.triZero F3.triZero
    (Boundary.e6 word) (Boundary.e7 word)
    (Boundary.e8 word) (Boundary.e9 word)
    (Boundary.e10 word) (Boundary.e11 word)

wordDecompose :
  (word : Boundary.Word12) →
  addWord (headOnly word) (tailOnly word) ≡ word
wordDecompose word =
  wordExt
    (F3.triAdd-identityʳ (Boundary.e0 word))
    (F3.triAdd-identityʳ (Boundary.e1 word))
    (F3.triAdd-identityʳ (Boundary.e2 word))
    (F3.triAdd-identityʳ (Boundary.e3 word))
    (F3.triAdd-identityʳ (Boundary.e4 word))
    (F3.triAdd-identityʳ (Boundary.e5 word))
    (F3.triAdd-identityˡ (Boundary.e6 word))
    (F3.triAdd-identityˡ (Boundary.e7 word))
    (F3.triAdd-identityˡ (Boundary.e8 word))
    (F3.triAdd-identityˡ (Boundary.e9 word))
    (F3.triAdd-identityˡ (Boundary.e10 word))
    (F3.triAdd-identityˡ (Boundary.e11 word))

tailMessage : Boundary.Word12 → Boundary.Message6
tailMessage word =
  Boundary.vec6
    (Boundary.e6 word) (Boundary.e7 word)
    (Boundary.e8 word) (Boundary.e9 word)
    (Boundary.e10 word) (Boundary.e11 word)

tailFromMessage : Boundary.Message6 → Boundary.Word12
tailFromMessage message =
  Boundary.vec12
    F3.triZero F3.triZero F3.triZero
    F3.triZero F3.triZero F3.triZero
    (Boundary.c0 message) (Boundary.c1 message)
    (Boundary.c2 message) (Boundary.c3 message)
    (Boundary.c4 message) (Boundary.c5 message)

tailCanonical :
  (word : Boundary.Word12) →
  tailFromMessage (tailMessage word) ≡ tailOnly word
tailCanonical
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = refl

zeroLike : List TriTruth → List TriTruth
zeroLike [] = []
zeroLike (x ∷ xs) = F3.triZero ∷ zeroLike xs

dotZeroRightLike :
  (values : List TriTruth) →
  Linear.dotList values (zeroLike values) ≡ F3.triZero
dotZeroRightLike [] = refl
dotZeroRightLike (x ∷ xs) =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (F3.triMul-zeroʳ x)
      (dotZeroRightLike xs))
    refl

dotSkipZero :
  (x : TriTruth) (xs ys : List TriTruth) →
  Linear.dotList (x ∷ xs) (F3.triZero ∷ ys)
  ≡ Linear.dotList xs ys
dotSkipZero x xs ys =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (F3.triMul-zeroʳ x)
      refl)
    (F3.triAdd-identityˡ (Linear.dotList xs ys))

dotOneThenZeros :
  (x : TriTruth) (xs : List TriTruth) →
  Linear.dotList (x ∷ xs) (F3.triOne ∷ zeroLike xs)
  ≡ x
dotOneThenZeros x xs =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (F3.triMul-identityʳ x)
      (dotZeroRightLike xs))
    (F3.triAdd-identityʳ x)

dotBasis0 :
  (x0 x1 x2 x3 x4 x5 : TriTruth) →
  Linear.dotList
    (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
    (F3.triOne ∷ F3.triZero ∷ F3.triZero ∷
     F3.triZero ∷ F3.triZero ∷ F3.triZero ∷ [])
  ≡ x0
dotBasis0 x0 x1 x2 x3 x4 x5 =
  dotOneThenZeros x0 (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])

dotBasis1 :
  (x0 x1 x2 x3 x4 x5 : TriTruth) →
  Linear.dotList
    (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
    (F3.triZero ∷ F3.triOne ∷ F3.triZero ∷
     F3.triZero ∷ F3.triZero ∷ F3.triZero ∷ [])
  ≡ x1
dotBasis1 x0 x1 x2 x3 x4 x5 =
  Linear.trans
    (dotSkipZero x0
      (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
      (F3.triOne ∷ F3.triZero ∷ F3.triZero ∷
       F3.triZero ∷ F3.triZero ∷ []))
    (dotOneThenZeros x1 (x2 ∷ x3 ∷ x4 ∷ x5 ∷ []))

dotBasis2 :
  (x0 x1 x2 x3 x4 x5 : TriTruth) →
  Linear.dotList
    (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
    (F3.triZero ∷ F3.triZero ∷ F3.triOne ∷
     F3.triZero ∷ F3.triZero ∷ F3.triZero ∷ [])
  ≡ x2
dotBasis2 x0 x1 x2 x3 x4 x5 =
  Linear.trans
    (dotSkipZero x0
      (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
      (F3.triZero ∷ F3.triOne ∷ F3.triZero ∷
       F3.triZero ∷ F3.triZero ∷ []))
    (Linear.trans
      (dotSkipZero x1
        (x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
        (F3.triOne ∷ F3.triZero ∷ F3.triZero ∷
         F3.triZero ∷ []))
      (dotOneThenZeros x2 (x3 ∷ x4 ∷ x5 ∷ [])))

dotBasis3 :
  (x0 x1 x2 x3 x4 x5 : TriTruth) →
  Linear.dotList
    (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
    (F3.triZero ∷ F3.triZero ∷ F3.triZero ∷
     F3.triOne ∷ F3.triZero ∷ F3.triZero ∷ [])
  ≡ x3
dotBasis3 x0 x1 x2 x3 x4 x5 =
  Linear.trans
    (dotSkipZero x0
      (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
      (F3.triZero ∷ F3.triZero ∷ F3.triOne ∷
       F3.triZero ∷ F3.triZero ∷ []))
    (Linear.trans
      (dotSkipZero x1
        (x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
        (F3.triZero ∷ F3.triOne ∷ F3.triZero ∷
         F3.triZero ∷ []))
      (Linear.trans
        (dotSkipZero x2
          (x3 ∷ x4 ∷ x5 ∷ [])
          (F3.triOne ∷ F3.triZero ∷ F3.triZero ∷ []))
        (dotOneThenZeros x3 (x4 ∷ x5 ∷ []))))

dotBasis4 :
  (x0 x1 x2 x3 x4 x5 : TriTruth) →
  Linear.dotList
    (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
    (F3.triZero ∷ F3.triZero ∷ F3.triZero ∷
     F3.triZero ∷ F3.triOne ∷ F3.triZero ∷ [])
  ≡ x4
dotBasis4 x0 x1 x2 x3 x4 x5 =
  Linear.trans
    (dotSkipZero x0
      (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
      (F3.triZero ∷ F3.triZero ∷ F3.triZero ∷
       F3.triOne ∷ F3.triZero ∷ []))
    (Linear.trans
      (dotSkipZero x1
        (x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
        (F3.triZero ∷ F3.triZero ∷ F3.triOne ∷
         F3.triZero ∷ []))
      (Linear.trans
        (dotSkipZero x2
          (x3 ∷ x4 ∷ x5 ∷ [])
          (F3.triZero ∷ F3.triOne ∷ F3.triZero ∷ []))
        (Linear.trans
          (dotSkipZero x3
            (x4 ∷ x5 ∷ [])
            (F3.triOne ∷ F3.triZero ∷ []))
          (dotOneThenZeros x4 (x5 ∷ [])))))

dotBasis5 :
  (x0 x1 x2 x3 x4 x5 : TriTruth) →
  Linear.dotList
    (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
    (F3.triZero ∷ F3.triZero ∷ F3.triZero ∷
     F3.triZero ∷ F3.triZero ∷ F3.triOne ∷ [])
  ≡ x5
dotBasis5 x0 x1 x2 x3 x4 x5 =
  Linear.trans
    (dotSkipZero x0
      (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
      (F3.triZero ∷ F3.triZero ∷ F3.triZero ∷
       F3.triZero ∷ F3.triOne ∷ []))
    (Linear.trans
      (dotSkipZero x1
        (x2 ∷ x3 ∷ x4 ∷ x5 ∷ [])
        (F3.triZero ∷ F3.triZero ∷ F3.triZero ∷
         F3.triOne ∷ []))
      (Linear.trans
        (dotSkipZero x2
          (x3 ∷ x4 ∷ x5 ∷ [])
          (F3.triZero ∷ F3.triZero ∷ F3.triOne ∷ []))
        (Linear.trans
          (dotSkipZero x3
            (x4 ∷ x5 ∷ [])
            (F3.triZero ∷ F3.triOne ∷ []))
          (Linear.trans
            (dotSkipZero x4
              (x5 ∷ [])
              (F3.triOne ∷ []))
            (dotOneThenZeros x5 [])))))

headDot0 headDot1 headDot2 headDot3 headDot4 headDot5 :
  (word : Boundary.Word12) → TriTruth
headDot0 word = wordDot (headOnly word) (Explicit.encode Explicit.basis0)
headDot1 word = wordDot (headOnly word) (Explicit.encode Explicit.basis1)
headDot2 word = wordDot (headOnly word) (Explicit.encode Explicit.basis2)
headDot3 word = wordDot (headOnly word) (Explicit.encode Explicit.basis3)
headDot4 word = wordDot (headOnly word) (Explicit.encode Explicit.basis4)
headDot5 word = wordDot (headOnly word) (Explicit.encode Explicit.basis5)

headDot0Select : (word : Boundary.Word12) → headDot0 word ≡ Boundary.e0 word
headDot0Select
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (dotBasis0 x0 x1 x2 x3 x4 x5)
      refl)
    (F3.triAdd-identityʳ x0)

headDot1Select : (word : Boundary.Word12) → headDot1 word ≡ Boundary.e1 word
headDot1Select
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (dotBasis1 x0 x1 x2 x3 x4 x5)
      refl)
    (F3.triAdd-identityʳ x1)

headDot2Select : (word : Boundary.Word12) → headDot2 word ≡ Boundary.e2 word
headDot2Select
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (dotBasis2 x0 x1 x2 x3 x4 x5)
      refl)
    (F3.triAdd-identityʳ x2)

headDot3Select : (word : Boundary.Word12) → headDot3 word ≡ Boundary.e3 word
headDot3Select
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (dotBasis3 x0 x1 x2 x3 x4 x5)
      refl)
    (F3.triAdd-identityʳ x3)

headDot4Select : (word : Boundary.Word12) → headDot4 word ≡ Boundary.e4 word
headDot4Select
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (dotBasis4 x0 x1 x2 x3 x4 x5)
      refl)
    (F3.triAdd-identityʳ x4)

headDot5Select : (word : Boundary.Word12) → headDot5 word ≡ Boundary.e5 word
headDot5Select
  (Boundary.vec12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) =
  Linear.trans
    (Linear.cong₂ F3.triAdd
      (dotBasis5 x0 x1 x2 x3 x4 x5)
      refl)
    (F3.triAdd-identityʳ x5)

tailContribution0 tailContribution1 tailContribution2
  tailContribution3 tailContribution4 tailContribution5 :
  Boundary.Word12 → TriTruth
tailContribution0 word = wordDot (tailOnly word) (Explicit.encode Explicit.basis0)
tailContribution1 word = wordDot (tailOnly word) (Explicit.encode Explicit.basis1)
tailContribution2 word = wordDot (tailOnly word) (Explicit.encode Explicit.basis2)
tailContribution3 word = wordDot (tailOnly word) (Explicit.encode Explicit.basis3)
tailContribution4 word = wordDot (tailOnly word) (Explicit.encode Explicit.basis4)
tailContribution5 word = wordDot (tailOnly word) (Explicit.encode Explicit.basis5)

dotDecompose0 :
  (word : Boundary.Word12) →
  wordDot word (Explicit.encode Explicit.basis0)
  ≡ F3.triAdd (Boundary.e0 word) (tailContribution0 word)
dotDecompose0 word =
  Linear.trans
    (Linear.cong
      (λ value → wordDot value (Explicit.encode Explicit.basis0))
      (Linear.sym (wordDecompose word)))
    (Linear.trans
      (wordDotAddLeft
        (headOnly word) (tailOnly word)
        (Explicit.encode Explicit.basis0))
      (Linear.cong₂ F3.triAdd (headDot0Select word) refl))

dotDecompose1 :
  (word : Boundary.Word12) →
  wordDot word (Explicit.encode Explicit.basis1)
  ≡ F3.triAdd (Boundary.e1 word) (tailContribution1 word)
dotDecompose1 word =
  Linear.trans
    (Linear.cong
      (λ value → wordDot value (Explicit.encode Explicit.basis1))
      (Linear.sym (wordDecompose word)))
    (Linear.trans
      (wordDotAddLeft
        (headOnly word) (tailOnly word)
        (Explicit.encode Explicit.basis1))
      (Linear.cong₂ F3.triAdd (headDot1Select word) refl))

dotDecompose2 :
  (word : Boundary.Word12) →
  wordDot word (Explicit.encode Explicit.basis2)
  ≡ F3.triAdd (Boundary.e2 word) (tailContribution2 word)
dotDecompose2 word =
  Linear.trans
    (Linear.cong
      (λ value → wordDot value (Explicit.encode Explicit.basis2))
      (Linear.sym (wordDecompose word)))
    (Linear.trans
      (wordDotAddLeft
        (headOnly word) (tailOnly word)
        (Explicit.encode Explicit.basis2))
      (Linear.cong₂ F3.triAdd (headDot2Select word) refl))

dotDecompose3 :
  (word : Boundary.Word12) →
  wordDot word (Explicit.encode Explicit.basis3)
  ≡ F3.triAdd (Boundary.e3 word) (tailContribution3 word)
dotDecompose3 word =
  Linear.trans
    (Linear.cong
      (λ value → wordDot value (Explicit.encode Explicit.basis3))
      (Linear.sym (wordDecompose word)))
    (Linear.trans
      (wordDotAddLeft
        (headOnly word) (tailOnly word)
        (Explicit.encode Explicit.basis3))
      (Linear.cong₂ F3.triAdd (headDot3Select word) refl))

dotDecompose4 :
  (word : Boundary.Word12) →
  wordDot word (Explicit.encode Explicit.basis4)
  ≡ F3.triAdd (Boundary.e4 word) (tailContribution4 word)
dotDecompose4 word =
  Linear.trans
    (Linear.cong
      (λ value → wordDot value (Explicit.encode Explicit.basis4))
      (Linear.sym (wordDecompose word)))
    (Linear.trans
      (wordDotAddLeft
        (headOnly word) (tailOnly word)
        (Explicit.encode Explicit.basis4))
      (Linear.cong₂ F3.triAdd (headDot4Select word) refl))

dotDecompose5 :
  (word : Boundary.Word12) →
  wordDot word (Explicit.encode Explicit.basis5)
  ≡ F3.triAdd (Boundary.e5 word) (tailContribution5 word)
dotDecompose5 word =
  Linear.trans
    (Linear.cong
      (λ value → wordDot value (Explicit.encode Explicit.basis5))
      (Linear.sym (wordDecompose word)))
    (Linear.trans
      (wordDotAddLeft
        (headOnly word) (tailOnly word)
        (Explicit.encode Explicit.basis5))
      (Linear.cong₂ F3.triAdd (headDot5Select word) refl))

solveAddRightZero :
  (a b : TriTruth) →
  F3.triAdd a b ≡ F3.triZero →
  a ≡ F3.triNeg b
solveAddRightZero a b equality =
  Linear.trans
    (Linear.sym (F3.triAdd-identityʳ a))
    (Linear.trans
      (Linear.cong (F3.triAdd a)
        (Linear.sym (F3.triAdd-inverseʳ b)))
      (Linear.trans
        (F3.triAdd-assoc a b (F3.triNeg b))
        (Linear.trans
          (Linear.cong
            (λ value → F3.triAdd value (F3.triNeg b))
            equality)
          (F3.triAdd-identityˡ (F3.triNeg b)))))

dualMessage : Boundary.Message6 → Boundary.Message6
dualMessage tail =
  let word = tailFromMessage tail in
  Boundary.vec6
    (F3.triNeg (tailContribution0 word))
    (F3.triNeg (tailContribution1 word))
    (F3.triNeg (tailContribution2 word))
    (F3.triNeg (tailContribution3 word))
    (F3.triNeg (tailContribution4 word))
    (F3.triNeg (tailContribution5 word))

dualEncode : Boundary.Message6 → Boundary.Word12
dualEncode tail =
  let head = dualMessage tail in
  Boundary.vec12
    (Boundary.c0 head) (Boundary.c1 head)
    (Boundary.c2 head) (Boundary.c3 head)
    (Boundary.c4 head) (Boundary.c5 head)
    (Boundary.c0 tail) (Boundary.c1 tail)
    (Boundary.c2 tail) (Boundary.c3 tail)
    (Boundary.c4 tail) (Boundary.c5 tail)

dualCandidateCodeCheck : Bool
dualCandidateCodeCheck =
  allList
    (λ tail →
      wordEq
        (Explicit.encode (dualMessage tail))
        (dualEncode tail))
    Explicit.allMessages

dualCandidateCodeCheckIsTrue : dualCandidateCodeCheck ≡ true
dualCandidateCodeCheckIsTrue = refl

dualCandidateIsCode :
  (tail : Boundary.Message6) →
  Explicit.encode (dualMessage tail) ≡ dualEncode tail
dualCandidateIsCode tail =
  wordEqSound
    (allListMember
      (allMessagesComplete tail)
      dualCandidateCodeCheckIsTrue)

dualRows :
  ∀ {word} →
  CodeDualMember word →
  AllDotsZero word Explicit.generatorRows
dualRows dualMember =
  allDotsCons
    (dualMember (codeMember Explicit.basis0 refl))
    (allDotsCons
      (dualMember (codeMember Explicit.basis1 refl))
      (allDotsCons
        (dualMember (codeMember Explicit.basis2 refl))
        (allDotsCons
          (dualMember (codeMember Explicit.basis3 refl))
          (allDotsCons
            (dualMember (codeMember Explicit.basis4 refl))
            (allDotsCons
              (dualMember (codeMember Explicit.basis5 refl))
              allDotsNil)))))

dualNormalForm :
  (word : Boundary.Word12) →
  AllDotsZero word Explicit.generatorRows →
  dualEncode (tailMessage word) ≡ word
dualNormalForm word
  (allDotsCons h0
    (allDotsCons h1
      (allDotsCons h2
        (allDotsCons h3
          (allDotsCons h4
            (allDotsCons h5 allDotsNil)))))) =
  wordExt
    (Linear.trans
      (Linear.cong F3.triNeg
        (Linear.cong
          (λ tail → wordDot tail (Explicit.encode Explicit.basis0))
          (tailCanonical word)))
      (Linear.sym
        (solveAddRightZero
          (Boundary.e0 word)
          (tailContribution0 word)
          (Linear.trans (Linear.sym (dotDecompose0 word)) h0))))
    (Linear.trans
      (Linear.cong F3.triNeg
        (Linear.cong
          (λ tail → wordDot tail (Explicit.encode Explicit.basis1))
          (tailCanonical word)))
      (Linear.sym
        (solveAddRightZero
          (Boundary.e1 word)
          (tailContribution1 word)
          (Linear.trans (Linear.sym (dotDecompose1 word)) h1))))
    (Linear.trans
      (Linear.cong F3.triNeg
        (Linear.cong
          (λ tail → wordDot tail (Explicit.encode Explicit.basis2))
          (tailCanonical word)))
      (Linear.sym
        (solveAddRightZero
          (Boundary.e2 word)
          (tailContribution2 word)
          (Linear.trans (Linear.sym (dotDecompose2 word)) h2))))
    (Linear.trans
      (Linear.cong F3.triNeg
        (Linear.cong
          (λ tail → wordDot tail (Explicit.encode Explicit.basis3))
          (tailCanonical word)))
      (Linear.sym
        (solveAddRightZero
          (Boundary.e3 word)
          (tailContribution3 word)
          (Linear.trans (Linear.sym (dotDecompose3 word)) h3))))
    (Linear.trans
      (Linear.cong F3.triNeg
        (Linear.cong
          (λ tail → wordDot tail (Explicit.encode Explicit.basis4))
          (tailCanonical word)))
      (Linear.sym
        (solveAddRightZero
          (Boundary.e4 word)
          (tailContribution4 word)
          (Linear.trans (Linear.sym (dotDecompose4 word)) h4))))
    (Linear.trans
      (Linear.cong F3.triNeg
        (Linear.cong
          (λ tail → wordDot tail (Explicit.encode Explicit.basis5))
          (tailCanonical word)))
      (Linear.sym
        (solveAddRightZero
          (Boundary.e5 word)
          (tailContribution5 word)
          (Linear.trans (Linear.sym (dotDecompose5 word)) h5))))
    refl refl refl refl refl refl

dualToCode :
  ∀ {word} →
  CodeDualMember word →
  CodeMember word
dualToCode {word} dualMember =
  let tail = tailMessage word in
  codeMember
    (dualMessage tail)
    (Linear.trans
      (dualCandidateIsCode tail)
      (dualNormalForm word (dualRows dualMember)))

codeSubspace : Linear.F3Subspace wordSpace
codeSubspace = record
  { Member = CodeMember
  ; zeroMember =
      dualToCode (Linear.zeroMember dualSubspace)
  ; addMember = λ {left} {right} leftCode rightCode →
      dualToCode
        (Linear.addMember dualSubspace
          (codeToDual leftCode)
          (codeToDual rightCode))
  ; scaleMember = λ a {word} wordCode →
      dualToCode
        (Linear.scaleMember dualSubspace a
          (codeToDual wordCode))
  }

golaySelfDual : codeSubspace Linear.≈ₛ dualSubspace
golaySelfDual =
  Linear.selfDualFromInclusions
    codeSubspace dualSubspace
    codeToDual dualToCode

record GolaySelfDualSubspaceCertificate : Set where
  constructor golaySelfDualSubspaceCertificate
  field
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String
    generatorSpanEqualsSystematicEncoder :
      (message : Boundary.Message6) →
      spanEncode message ≡ Explicit.encode message
    everyEncodedWordOrthogonalToRows :
      (message : Boundary.Message6) →
      AllDotsZero (Explicit.encode message) Explicit.generatorRows
    dualSystematicNormalForm :
      (word : Boundary.Word12) →
      CodeDualMember word →
      dualEncode (tailMessage word) ≡ word
    concreteSelfDuality : codeSubspace Linear.≈ₛ dualSubspace

canonicalGolaySelfDualSubspaceCertificate :
  GolaySelfDualSubspaceCertificate
canonicalGolaySelfDualSubspaceCertificate =
  golaySelfDualSubspaceCertificate
    (Sources.author Sources.macWilliamsSloaneEntry)
    (Sources.title Sources.macWilliamsSloaneEntry)
    "no DOI recorded for the cited book"
    spanEncodeCorrect
    encodedWordOrthogonalToRows
    (λ word dualMember → dualNormalForm word (dualRows dualMember))
    golaySelfDual

golaySelfDualSubspaceReceipt : GenericReceipt.GenericReceipt
golaySelfDualSubspaceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "explicit ternary Golay finite-subspace self-duality"
    "DASHI.Foundations.TernaryGolay.GolaySelfDualSubspace"
    "canonicalGolaySelfDualSubspaceCertificate"
    "the explicit encoder image and its full coordinate-dot orthogonal complement are first-class F3 subspaces with proved mutual inclusion; the systematic dual normal form and generator-span identity are checked on the complete 729-message carrier"
    "the proof does not use uniqueness to infer self-duality, and it does not identify a conventional group or lattice merely from matching cardinalities"
    "agda -i . DASHI/Foundations/TernaryGolay/GolaySelfDualSubspace.agda"

golaySelfDualSubspaceReceiptNonPromoting :
  GenericReceipt.promotesClaim golaySelfDualSubspaceReceipt ≡ false
golaySelfDualSubspaceReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse golaySelfDualSubspaceReceipt
