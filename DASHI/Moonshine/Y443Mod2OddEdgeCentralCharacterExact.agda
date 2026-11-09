{-# OPTIONS --safe #-}
module DASHI.Moonshine.Y443Mod2OddEdgeCentralCharacterExact where

------------------------------------------------------------------------
-- The actual Y443 graph's eleven ODD Coxeter edge constraints and the
-- odd seven-node central word have only the trivial Z/2 character.
--
-- These are extracted algebraic CONSEQUENCES of original relations,
-- NOT a selected-group kernel-reflection or Monster identification.
-- A separate exact finite regression verifies these are the actual
-- mod-2 images of the source's 79/80 words.
--
-- Attribution: Ivanov/Bray/TauCeti for Y443 source; DASHI
-- characteristic-two graph/central computation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
open import Agda.Builtin.Nat using (Nat; suc)

infixl 6 _⊕_
_⊕_ : Bool → Bool → Bool
false ⊕ b = b
true ⊕ false = true
true ⊕ true = false

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

xorZeroMeansEqual : ∀ a b → a ⊕ b ≡ false → a ≡ b
xorZeroMeansEqual false false p = refl
xorZeroMeansEqual false true ()
xorZeroMeansEqual true false ()
xorZeroMeansEqual true true p = refl

sevenOdd : ∀ x →
  x ⊕ (x ⊕ (x ⊕ (x ⊕ (x ⊕ (x ⊕ (x ⊕ false)))))) ≡ x
sevenOdd false = refl
sevenOdd true = refl


------------------------------------------------------------------------
-- Normalize the ACTUAL source central relation (the 9th power of its
-- seven-node word) using characteristic-two word parity. This discharges
-- the central-word transcription rather than assuming the 7-bit parity.
------------------------------------------------------------------------

parityWord : (Y.Node → Bool) → Y.Word → Bool
parityWord q [] = false
parityWord q (n ∷ ns) = q n ⊕ parityWord q ns

xorAssoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
xorAssoc false false false = refl
xorAssoc false false true = refl
xorAssoc false true false = refl
xorAssoc false true true = refl
xorAssoc true false false = refl
xorAssoc true false true = refl
xorAssoc true true false = refl
xorAssoc true true true = refl

xorTwice : ∀ a b → a ⊕ (a ⊕ b) ≡ b
xorTwice false false = refl
xorTwice false true = refl
xorTwice true false = refl
xorTwice true true = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
cong f refl = refl

parityAppend :
  (q : Y.Node → Bool) (left right : Y.Word) →
  parityWord q (Y._++_ left right)
    ≡ parityWord q left ⊕ parityWord q right
parityAppend q [] ys = refl
parityAppend q (x ∷ xs) ys =
  trans
    (cong (λ z → q x ⊕ z) (parityAppend q xs ys))
    (sym (xorAssoc (q x) (parityWord q xs) (parityWord q ys)))

parityPowerTwoStep :
  (q : Y.Node → Bool) (w : Y.Word) (n : Nat) →
  parityWord q (Y.powerWord w (suc (Agda.Builtin.Nat.suc n)))
    ≡ parityWord q (Y.powerWord w n)
parityPowerTwoStep q w n =
  trans
    (parityAppend q w (Y.powerWord w (Agda.Builtin.Nat.suc n)))
    (trans
      (cong (λ z → parityWord q w ⊕ z)
        (parityAppend q w (Y.powerWord w n)))
      (xorTwice (parityWord q w) (parityWord q (Y.powerWord w n))))

module Selected (charge : Y.Node → Bool) where

  centralParity : Bool
  centralParity =
    charge Y.a ⊕
    (charge Y.b3 ⊕
    (charge Y.c3 ⊕
    (charge Y.d3 ⊕
    (charge Y.b1 ⊕
    (charge Y.c1 ⊕
    (charge Y.b2 ⊕ false))))))

  sourceCentralPowerNineParity :
    parityWord charge Y.centralInvolutionRelator ≡ centralParity
  sourceCentralPowerNineParity =
    trans (parityPowerTwoStep charge Y.centralBase 7)
      (trans (parityPowerTwoStep charge Y.centralBase 5)
        (trans (parityPowerTwoStep charge Y.centralBase 3)
          (trans (parityPowerTwoStep charge Y.centralBase 1) refl)))

  -- This removes the previously open central side of the
  -- source-word -> parity-record bridge. Only actual eleven edge
  -- relator membership/odd exponent transport remains to be welded.

  record SourceEdgeCentralParity : Set where
    field
      ab1 : charge Y.a ⊕ charge Y.b1 ≡ false
      b1c1 : charge Y.b1 ⊕ charge Y.c1 ≡ false
      c1d1 : charge Y.c1 ⊕ charge Y.d1 ≡ false
      d1e1 : charge Y.d1 ⊕ charge Y.e1 ≡ false
      ab2 : charge Y.a ⊕ charge Y.b2 ≡ false
      b2c2 : charge Y.b2 ⊕ charge Y.c2 ≡ false
      c2d2 : charge Y.c2 ⊕ charge Y.d2 ≡ false
      d2e2 : charge Y.d2 ⊕ charge Y.e2 ≡ false
      ab3 : charge Y.a ⊕ charge Y.b3 ≡ false
      b3c3 : charge Y.b3 ⊕ charge Y.c3 ≡ false
      c3d3 : charge Y.c3 ⊕ charge Y.d3 ≡ false
      centralOddZero : centralParity ≡ false

  open SourceEdgeCentralParity public

  allNodesSameParity :
    (source : SourceEdgeCentralParity) →
    (n : Y.Node) → charge n ≡ charge Y.a
  allNodesSameParity src Y.a = refl
  allNodesSameParity src Y.b1 =
    sym (xorZeroMeansEqual _ _ (ab1 src))
  allNodesSameParity src Y.c1 =
    trans
      (sym (xorZeroMeansEqual _ _ (b1c1 src)))
      (allNodesSameParity src Y.b1)
  allNodesSameParity src Y.d1 =
    trans
      (sym (xorZeroMeansEqual _ _ (c1d1 src)))
      (allNodesSameParity src Y.c1)
  allNodesSameParity src Y.e1 =
    trans
      (sym (xorZeroMeansEqual _ _ (d1e1 src)))
      (allNodesSameParity src Y.d1)
  allNodesSameParity src Y.b2 =
    sym (xorZeroMeansEqual _ _ (ab2 src))
  allNodesSameParity src Y.c2 =
    trans
      (sym (xorZeroMeansEqual _ _ (b2c2 src)))
      (allNodesSameParity src Y.b2)
  allNodesSameParity src Y.d2 =
    trans
      (sym (xorZeroMeansEqual _ _ (c2d2 src)))
      (allNodesSameParity src Y.c2)
  allNodesSameParity src Y.e2 =
    trans
      (sym (xorZeroMeansEqual _ _ (d2e2 src)))
      (allNodesSameParity src Y.d2)
  allNodesSameParity src Y.b3 =
    sym (xorZeroMeansEqual _ _ (ab3 src))
  allNodesSameParity src Y.c3 =
    trans
      (sym (xorZeroMeansEqual _ _ (b3c3 src)))
      (allNodesSameParity src Y.b3)
  allNodesSameParity src Y.d3 =
    trans
      (sym (xorZeroMeansEqual _ _ (c3d3 src)))
      (allNodesSameParity src Y.c3)

  centralParityIsRoot :
    (source : SourceEdgeCentralParity) →
    centralParity ≡ charge Y.a
  centralParityIsRoot src
    rewrite allNodesSameParity src Y.b3
          | allNodesSameParity src Y.c3
          | allNodesSameParity src Y.d3
          | allNodesSameParity src Y.b1
          | allNodesSameParity src Y.c1
          | allNodesSameParity src Y.b2 =
    sevenOdd (charge Y.a)

  allNodeChargesTrivial :
    (source : SourceEdgeCentralParity) →
    (n : Y.Node) → charge n ≡ false
  allNodeChargesTrivial src n =
    trans (allNodesSameParity src n)
      (trans (sym (centralParityIsRoot src))
        (centralOddZero src))
