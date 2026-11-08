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
         *-assoc; *-comm; *-distribˡ-+; *-distribʳ-+;
         mulZeroʳ; mulZeroˡ)
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


  ----------------------------------------------------------------------
  -- FULL FINITE WILSON PRODUCT ALGEBRA: THE REMAINING LOGICAL SOURCE
  -- IS GENUINE ORIGINAL LOOP-WORD CONCATENATION.
  --
  -- Products of two finite linear combinations use literal ordered
  -- concatenation of loop words. This is NOT a new physical Wilson
  -- multiplication: the law below requires it to be equal pointwise to
  -- multiplication of the ORIGINAL normalized Wilson loop products.
  -- All coefficient distributivity, sums, and cross-product bookkeeping
  -- are then THEOREMS from the existing real ring.
  ----------------------------------------------------------------------

  module WithOriginalWordProduct
    (actualWordConcat :
      (left right : List Loop) (configuration : Configuration) →
      Wilson.productLoopObservable originalWilson
        (left ++ right) configuration
      ≡ Wilson.productLoopObservable originalWilson left configuration
        *ℝ Wilson.productLoopObservable originalWilson right configuration)
    where

    crossRow : ℝ → List Loop → LiteralWilsonSpan → LiteralWilsonSpan
    crossRow a words =
      map (λ { (b , other) → (a *ℝ b , words ++ other) })

    mulSpan : LiteralWilsonSpan → LiteralWilsonSpan → LiteralWilsonSpan
    mulSpan [] right = []
    mulSpan ((a , words) ∷ left) right =
      crossRow a words right ++ mulSpan left right

    coefficientExchange :
      (a b x y : ℝ) →
      (a *ℝ b) *ℝ (x *ℝ y)
      ≡ (a *ℝ x) *ℝ (b *ℝ y)
    coefficientExchange a b x y =
      trans
        (sym (*-assoc (a *ℝ b) x y))
        (trans
          (cong (λ t → t *ℝ y) (*-assoc a b x))
          (trans
            (cong (λ t → (a *ℝ t) *ℝ y) (*-comm b x))
            (trans
              (cong (λ t → t *ℝ y)
                (sym (*-assoc a x b)))
              (*-assoc (a *ℝ x) b y))))

    crossRowEmbedsProduct :
      (a : ℝ) (words : List Loop)
      (right : LiteralWilsonSpan) (configuration : Configuration) →
      embed (crossRow a words right) configuration
      ≡
      (a *ℝ Wilson.productLoopObservable
        originalWilson words configuration)
      *ℝ embed right configuration
    crossRowEmbedsProduct a words [] configuration =
      sym (mulZeroʳ
        (a *ℝ Wilson.productLoopObservable
          originalWilson words configuration))
    crossRowEmbedsProduct a words
      ((b , other) ∷ right) configuration =
      let
        x = Wilson.productLoopObservable originalWilson words configuration
        y = Wilson.productLoopObservable originalWilson other configuration
        targetHead = (a *ℝ x) *ℝ (b *ℝ y)
      in
      trans
        (cong (λ w →
          (a *ℝ b) *ℝ w +ℝ
            embed (crossRow a words right) configuration)
          (actualWordConcat words other configuration))
        (trans
          (cong (λ z →
            z +ℝ embed (crossRow a words right) configuration)
            (coefficientExchange a b x y))
          (trans
            (cong (λ z → targetHead +ℝ z)
              (crossRowEmbedsProduct a words right configuration))
            (sym (*-distribˡ-+ (a *ℝ x)
              (b *ℝ y) (embed right configuration)))))

    mulSpanEmbedsPointwise :
      (left right : LiteralWilsonSpan)
      (configuration : Configuration) →
      embed (mulSpan left right) configuration
      ≡ embed left configuration *ℝ embed right configuration
    mulSpanEmbedsPointwise [] right configuration =
      sym (mulZeroˡ (embed right configuration))
    mulSpanEmbedsPointwise
      ((a , words) ∷ left) right configuration =
      let head = a *ℝ Wilson.productLoopObservable
            originalWilson words configuration
      in
      trans
        (appendSpanEmbedsSum
          (crossRow a words right) (mulSpan left right) configuration)
        (trans
          (cong (λ z →
            z +ℝ embed (mulSpan left right) configuration)
            (crossRowEmbedsProduct a words right configuration))
          (trans
            (cong (λ z →
              head *ℝ embed right configuration +ℝ z)
              (mulSpanEmbedsPointwise left right configuration))
            (sym (*-distribʳ-+ head
              (embed left configuration)
              (embed right configuration)))))

    -- The actual R583 embedsCylinderProduct asks for function equality,
    -- not merely pointwise equality. Its final step requires the
    -- function-extensionality principle for the same selected carrier,
    -- and proof that OS2 multiplication IS original pointwise product.
    mulSpanEmbedsOriginalObservable :
      (functionExtensionality :
        ∀ (f g : Configuration → ℝ) →
        ((configuration : Configuration) → f configuration ≡ g configuration)
        → f ≡ g) →
      (left right : LiteralWilsonSpan) →
      embed (mulSpan left right)
      ≡ (λ configuration →
          embed left configuration *ℝ embed right configuration)
    mulSpanEmbedsOriginalObservable funext left right =
      funext
        (embed (mulSpan left right))
        (λ configuration →
          embed left configuration *ℝ embed right configuration)
        (mulSpanEmbedsPointwise left right)
