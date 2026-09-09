module DASHI.Moonshine.JInvariantOrderThreeScaleGlobalInjectiveExact where

------------------------------------------------------------------------
-- GLOBAL INJECTIVITY OF THE ORDER-THREE SEAM SCALE
--
--   D_k = k^2 + k + 1.
--
-- The visible-eight owner proved injectivity by finite elimination.  This file
-- removes that restriction: D is strictly increasing on all Nat.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale

------------------------------------------------------------------------
-- 1. Ordinary monotonicity of k^2+k+1.
------------------------------------------------------------------------

seamScaleMonotone :
  {left right : Nat} →
  left ≤ right →
  Scale.seamScale left ≤ Scale.seamScale right
seamScaleMonotone left≤right =
  NatP.+-mono-≤
    (NatP.+-mono-≤
      (NatP.*-mono-≤ left≤right left≤right)
      left≤right)
    NatP.≤-refl

------------------------------------------------------------------------
-- 2. Exact positive successor gap.
--
--   suc(D_k) + (2k+1) = D_(k+1).
------------------------------------------------------------------------

seamScaleSuccessorGap :
  (k : Nat) →
  suc (Scale.seamScale k) + suc (k + k)
  ≡ Scale.seamScale (suc k)
seamScaleSuccessorGap k =
  solve 1
    (λ k →
      ((con 1 :+ (((k :* k) :+ k) :+ con 1)) :+
       (con 1 :+ (k :+ k)))
      :=
      ((((con 1 :+ k) :* (con 1 :+ k)) :+
        (con 1 :+ k)) :+ con 1))
    refl k

seamScaleStrictStep :
  (k : Nat) →
  Scale.seamScale k < Scale.seamScale (suc k)
seamScaleStrictStep k =
  let
    raw :
      suc (Scale.seamScale k)
      ≤ suc (Scale.seamScale k) + suc (k + k)
    raw = NatP.m≤m+n
      (suc (Scale.seamScale k))
      (suc (k + k))
  in
  subst
    (λ right → suc (Scale.seamScale k) ≤ right)
    (seamScaleSuccessorGap k)
    raw

------------------------------------------------------------------------
-- 3. Strict order preservation on arbitrary indices.
------------------------------------------------------------------------

seamScalePreservesStrictOrder :
  {left right : Nat} →
  left < right →
  Scale.seamScale left < Scale.seamScale right
seamScalePreservesStrictOrder {left} {right} left<right =
  NatP.≤-trans
    (seamScaleStrictStep left)
    (seamScaleMonotone left<right)

------------------------------------------------------------------------
-- 4. Global injectivity by Nat trichotomy.
------------------------------------------------------------------------

seamScaleInjective :
  (left right : Nat) →
  Scale.seamScale left ≡ Scale.seamScale right →
  left ≡ right
seamScaleInjective left right same
  with NatP.<-cmp left right
... | tri≈ left≡right _ _ = left≡right
... | tri< left<right _ _ =
  ⊥-elim
    (NatP.<-irrefl
      (Scale.seamScale right)
      (subst
        (λ x → x < Scale.seamScale right)
        same
        (seamScalePreservesStrictOrder left<right)))
... | tri> _ _ right<left =
  ⊥-elim
    (NatP.<-irrefl
      (Scale.seamScale right)
      (subst
        (λ x → Scale.seamScale right < x)
        same
        (seamScalePreservesStrictOrder right<left)))

------------------------------------------------------------------------
-- 5. Exact recognition theorem: same measured exact scale means same k.
------------------------------------------------------------------------

record GlobalScaleRecognition : Set where
  constructor global-scale-recognition
  field
    recognisedIndex : Nat
    measuredScale : Nat
    scaleLaw : measuredScale ≡ Scale.seamScale recognisedIndex

open GlobalScaleRecognition public

sameExactScaleForcesSameIndex :
  (left right : GlobalScaleRecognition) →
  measuredScale left ≡ measuredScale right →
  recognisedIndex left ≡ recognisedIndex right
sameExactScaleForcesSameIndex left right same =
  seamScaleInjective
    (recognisedIndex left)
    (recognisedIndex right)
    (trans
      (sym (scaleLaw left))
      (trans same (scaleLaw right)))

record GlobalScaleInjectivityFrontier : Set where
  constructor global-scale-injectivity-frontier
  field
    forwardScaleExact : Bool
    scaleMonotoneAllNat : Bool
    scaleStrictlyIncreasingAllNat : Bool
    scaleInjectiveAllNat : Bool
    renderedBoxDeterminesExactScale : Bool

canonicalGlobalScaleInjectivityFrontier : GlobalScaleInjectivityFrontier
canonicalGlobalScaleInjectivityFrontier =
  global-scale-injectivity-frontier true true true true false
