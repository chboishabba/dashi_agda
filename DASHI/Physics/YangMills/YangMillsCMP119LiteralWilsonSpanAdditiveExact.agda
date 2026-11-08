{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCMP119LiteralWilsonSpanAdditiveExact where

------------------------------------------------------------------------
-- ROUND 583 / SOURCE-FIRST WILSON-TEST ADDITIVE AND SCALAR COMPILER
--
-- The original selected H1 OS4 observable class is ALREADY a literal
-- finite list of (real coefficient, finite Wilson loop word). Thus its
-- zero, sum and real scalar action are not new external theorem inputs:
--   zero = []
--   sum  = List._++_
--   scale c = List.map (lambda (a,loops) -> (c*a,loops)).
-- The embedding is EXACTLY the original R583.literalFiniteWilsonSpan.
-- Prove zero, additivity and scaling from the existing imported ordered
-- real ring laws. No new real axioms, no claims about H1 clustering,
-- OS Gram density, physical translation or Clay mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_; map)
open import Data.Product using (_×_; _,_)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; _+ℝ_; _*ℝ_; +-identityˡ; +-assoc;
         *-assoc; *-distribˡ-+; mulZeroʳ)
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Wilson
import DASHI.Physics.YangMills.YangMillsClayCMP119H1OS4AttachmentRound583Exact as H1

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

module Source {Loop Configuration : Set}
  (originalWilson :
    Wilson.WilsonCylinderBoundData Loop (Configuration → ℝ) ℝ) where

  WilsonWord : Set
  WilsonWord = ℝ × List Loop

  LiteralWilsonSpan : Set
  LiteralWilsonSpan = List WilsonWord

  embed : LiteralWilsonSpan → Configuration → ℝ
  embed = H1.literalFiniteWilsonSpan originalWilson

  zeroSpan : LiteralWilsonSpan
  zeroSpan = []

  addSpan : LiteralWilsonSpan → LiteralWilsonSpan → LiteralWilsonSpan
  addSpan = _++_

  scaleSpan : ℝ → LiteralWilsonSpan → LiteralWilsonSpan
  scaleSpan k = map (λ { (coefficient , loops) → (k *ℝ coefficient , loops) })

  emptySpanEmbedsZero : ∀ configuration →
    embed zeroSpan configuration ≡ 0ℝ
  emptySpanEmbedsZero configuration = refl

  appendSpanEmbedsSum :
    (left right : LiteralWilsonSpan) (configuration : Configuration) →
    embed (addSpan left right) configuration
    ≡ embed left configuration +ℝ embed right configuration
  appendSpanEmbedsSum [] right configuration =
    sym (+-identityˡ (embed right configuration))
  appendSpanEmbedsSum ((coefficient , loops) ∷ rest) right configuration =
    let head = coefficient *ℝ
          Wilson.productLoopObservable originalWilson loops configuration
    in trans
      (cong (λ tail → head +ℝ tail)
        (appendSpanEmbedsSum rest right configuration))
      (sym (+-assoc head
        (embed rest configuration) (embed right configuration)))

  scaleSpanEmbedsScalar :
    (k : ℝ) (terms : LiteralWilsonSpan) (configuration : Configuration) →
    embed (scaleSpan k terms) configuration
    ≡ k *ℝ embed terms configuration
  scaleSpanEmbedsScalar k [] configuration =
    sym (mulZeroʳ k)
  scaleSpanEmbedsScalar k ((coefficient , loops) ∷ rest) configuration =
    let observable =
          Wilson.productLoopObservable originalWilson loops configuration
        head = coefficient *ℝ observable
    in trans
      (cong (λ tail → (k *ℝ coefficient) *ℝ observable +ℝ tail)
        (scaleSpanEmbedsScalar k rest configuration))
      (trans
        (cong (λ x → x +ℝ k *ℝ embed rest configuration)
          (*-assoc k coefficient observable))
        (sym (*-distribˡ-+ k head (embed rest configuration))))
