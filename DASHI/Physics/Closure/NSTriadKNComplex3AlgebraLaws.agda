module DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Derived commutative-field, complex, and C3 algebra laws".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; these are direct consequences of the repository's
-- RealField interface.
-- Uses: exact additive cancellation, multiplication by zero, negation,
-- complex distributivity, bilinear-dot symmetry/right-linearity, and
-- Fourier mode-vector additivity.
-- Relationship: supplies the concrete algebra required to instantiate the
-- generic resonant-transverse derivative relocation theorem.  It does not
-- contain a Navier--Stokes estimate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

begin_ :
  ∀ {a : Level} {A : Set a} {x y : A} →
  x ≡ y → x ≡ y
begin proof = proof

_≡⟨_⟩_ :
  ∀ {a : Level} {A : Set a}
    (x : A) {y z : A} →
  x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ first ⟩ second = trans first second

_∎ :
  ∀ {a : Level} {A : Set a} (x : A) →
  x ≡ x
_ ∎ = refl

cong₂ :
  ∀ {a b c : Level}
    {A : Set a} {B : Set b} {C : Set c}
    (f : A → B → C)
    {x x' : A} {y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Derived real-field laws.
------------------------------------------------------------------------

realAddZeroRight :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.add F a (C3.zero F) ≡ a
realAddZeroRight F a =
  begin
    C3.add F a (C3.zero F)
  ≡⟨ C3.addCommutative F a (C3.zero F) ⟩
    C3.add F (C3.zero F) a
  ≡⟨ C3.addZeroLeft F a ⟩
    a
  ∎

realAddInverseRight :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.add F a (C3.negate F a) ≡ C3.zero F
realAddInverseRight F a =
  begin
    C3.add F a (C3.negate F a)
  ≡⟨ C3.addCommutative F a (C3.negate F a) ⟩
    C3.add F (C3.negate F a) a
  ≡⟨ C3.addInverseLeft F a ⟩
    C3.zero F
  ∎

realAddCancelLeft :
  ∀ {r} (F : C3.RealField r)
    (a b c : C3.Carrier F) →
  C3.add F a b ≡ C3.add F a c →
  b ≡ c
realAddCancelLeft F a b c equality =
  begin
    b
  ≡⟨ sym (C3.addZeroLeft F b) ⟩
    C3.add F (C3.zero F) b
  ≡⟨ cong (λ value → C3.add F value b)
       (sym (C3.addInverseLeft F a)) ⟩
    C3.add F (C3.add F (C3.negate F a) a) b
  ≡⟨ C3.addAssociative F (C3.negate F a) a b ⟩
    C3.add F (C3.negate F a) (C3.add F a b)
  ≡⟨ cong (C3.add F (C3.negate F a)) equality ⟩
    C3.add F (C3.negate F a) (C3.add F a c)
  ≡⟨ sym (C3.addAssociative F (C3.negate F a) a c) ⟩
    C3.add F (C3.add F (C3.negate F a) a) c
  ≡⟨ cong (λ value → C3.add F value c)
       (C3.addInverseLeft F a) ⟩
    C3.add F (C3.zero F) c
  ≡⟨ C3.addZeroLeft F c ⟩
    c
  ∎

realDistributeRight :
  ∀ {r} (F : C3.RealField r)
    (a b c : C3.Carrier F) →
  C3.multiply F (C3.add F a b) c
  ≡
  C3.add F
    (C3.multiply F a c)
    (C3.multiply F b c)
realDistributeRight F a b c =
  begin
    C3.multiply F (C3.add F a b) c
  ≡⟨ C3.multiplyCommutative F (C3.add F a b) c ⟩
    C3.multiply F c (C3.add F a b)
  ≡⟨ C3.distributeLeft F c a b ⟩
    C3.add F
      (C3.multiply F c a)
      (C3.multiply F c b)
  ≡⟨ cong₂ (C3.add F)
       (C3.multiplyCommutative F c a)
       (C3.multiplyCommutative F c b) ⟩
    C3.add F
      (C3.multiply F a c)
      (C3.multiply F b c)
  ∎

realMultiplyZeroLeft :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.multiply F (C3.zero F) a ≡ C3.zero F
realMultiplyZeroLeft F a =
  let
    product = C3.multiply F (C3.zero F) a

    duplicated :
      C3.add F product (C3.zero F)
      ≡
      C3.add F product product
    duplicated =
      begin
        C3.add F product (C3.zero F)
      ≡⟨ realAddZeroRight F product ⟩
        product
      ≡⟨ sym
          (cong (λ value → C3.multiply F value a)
            (C3.addZeroLeft F (C3.zero F))) ⟩
        C3.multiply F
          (C3.add F (C3.zero F) (C3.zero F))
          a
      ≡⟨ realDistributeRight F (C3.zero F) (C3.zero F) a ⟩
        C3.add F product product
      ∎
  in
  sym (realAddCancelLeft F product (C3.zero F) product duplicated)

realMultiplyZeroRight :
  ∀ {r} (F : C3.RealField r) (a : C3.Carrier F) →
  C3.multiply F a (C3.zero F) ≡ C3.zero F
realMultiplyZeroRight F a =
  begin
    C3.multiply F a (C3.zero F)
  ≡⟨ C3.multiplyCommutative F a (C3.zero F) ⟩
    C3.multiply F (C3.zero F) a
  ≡⟨ realMultiplyZeroLeft F a ⟩
    C3.zero F
  ∎

realNegateUniqueRight :
  ∀ {r} (F : C3.RealField r)
    (a b : C3.Carrier F) →
  C3.add F a b ≡ C3.zero F →
  b ≡ C3.negate F a
realNegateUniqueRight F a b inverse =
  begin
    b
  ≡⟨ sym (C3.addZeroLeft F b) ⟩
    C3.add F (C3.zero F) b
  ≡⟨ cong (λ value → C3.add F value b)
       (sym (C3.addInverseLeft F a)) ⟩
    C3.add F (C3.add F (C3.negate F a) a) b
  ≡⟨ C3.addAssociative F (C3.negate F a) a b ⟩
    C3.add F (C3.negate F a) (C3.add F a b)
  ≡⟨ cong (C3.add F (C3.negate F a)) inverse ⟩
    C3.add F (C3.negate F a) (C3.zero F)
  ≡⟨ realAddZeroRight F (C3.negate F a) ⟩
    C3.negate F a
  ∎

realNegateAdd :
  ∀ {r} (F : C3.RealField r)
    (a b : C3.Carrier F) →
  C3.negate F (C3.add F a b)
  ≡
  C3.add F (C3.negate F a) (C3.negate F b)
realNegateAdd F a b =
  let
    inverse :
      C3.add F
        (C3.add F a b)
        (C3.add F (C3.negate F a) (C3.negate F b))
      ≡ C3.zero F
    inverse =
      begin
        C3.add F
          (C3.add F a b)
          (C3.add F (C3.negate F a) (C3.negate F b))
      ≡⟨ C3.addAssociative F a b
          (C3.add F (C3.negate F a) (C3.negate F b)) ⟩
        C3.add F a
          (C3.add F b
            (C3.add F (C3.negate F a) (C3.negate F b)))
      ≡⟨ cong (C3.add F a)
          (sym (C3.addAssociative F b
            (C3.negate F a) (C3.negate F b))) ⟩
        C3.add F a
          (C3.add F
            (C3.add F b (C3.negate F a))
            (C3.negate F b))
      ≡⟨ cong (C3.add F a)
          (cong (λ value → C3.add F value (C3.negate F b))
            (C3.addCommutative F b (C3.negate F a))) ⟩
        C3.add F a
          (C3.add F
            (C3.add F (C3.negate F a) b)
            (C3.negate F b))
      ≡⟨ cong (C3.add F a)
          (C3.addAssociative F (C3.negate F a) b
            (C3.negate F b)) ⟩
        C3.add F a
          (C3.add F (C3.negate F a)
            (C3.add F b (C3.negate F b)))
      ≡⟨ cong (C3.add F a)
          (cong (C3.add F (C3.negate F a))
            (realAddInverseRight F b)) ⟩
        C3.add F a
          (C3.add F (C3.negate F a) (C3.zero F))
      ≡⟨ cong (C3.add F a)
          (realAddZeroRight F (C3.negate F a)) ⟩
        C3.add F a (C3.negate F a)
      ≡⟨ realAddInverseRight F a ⟩
        C3.zero F
      ∎
  in
  sym
    (realNegateUniqueRight F
      (C3.add F a b)
      (C3.add F (C3.negate F a) (C3.negate F b))
      inverse)

realNegateMultiplyLeft :
  ∀ {r} (F : C3.RealField r)
    (a b : C3.Carrier F) →
  C3.negate F (C3.multiply F a b)
  ≡
  C3.multiply F (C3.negate F a) b
realNegateMultiplyLeft F a b =
  let
    inverse :
      C3.add F
        (C3.multiply F a b)
        (C3.multiply F (C3.negate F a) b)
      ≡ C3.zero F
    inverse =
      begin
        C3.add F
          (C3.multiply F a b)
          (C3.multiply F (C3.negate F a) b)
      ≡⟨ sym (realDistributeRight F a (C3.negate F a) b) ⟩
        C3.multiply F
          (C3.add F a (C3.negate F a))
          b
      ≡⟨ cong (λ value → C3.multiply F value b)
          (realAddInverseRight F a) ⟩
        C3.multiply F (C3.zero F) b
      ≡⟨ realMultiplyZeroLeft F b ⟩
        C3.zero F
      ∎
  in
  sym
    (realNegateUniqueRight F
      (C3.multiply F a b)
      (C3.multiply F (C3.negate F a) b)
      inverse)

realNegateMultiplyRight :
  ∀ {r} (F : C3.RealField r)
    (a b : C3.Carrier F) →
  C3.negate F (C3.multiply F a b)
  ≡
  C3.multiply F a (C3.negate F b)
realNegateMultiplyRight F a b =
  begin
    C3.negate F (C3.multiply F a b)
  ≡⟨ cong (C3.negate F) (C3.multiplyCommutative F a b) ⟩
    C3.negate F (C3.multiply F b a)
  ≡⟨ realNegateMultiplyLeft F b a ⟩
    C3.multiply F (C3.negate F b) a
  ≡⟨ C3.multiplyCommutative F (C3.negate F b) a ⟩
    C3.multiply F a (C3.negate F b)
  ∎

realDoubleNegateProduct :
  ∀ {r} (F : C3.RealField r)
    (a b : C3.Carrier F) →
  C3.multiply F (C3.negate F a) (C3.negate F b)
  ≡ C3.multiply F a b
realDoubleNegateProduct F a b =
  begin
    C3.multiply F (C3.negate F a) (C3.negate F b)
  ≡⟨ sym (realNegateMultiplyLeft F a (C3.negate F b)) ⟩
    C3.negate F
      (C3.multiply F a (C3.negate F b))
  ≡⟨ cong (C3.negate F)
      (sym (realNegateMultiplyRight F a b)) ⟩
    C3.negate F (C3.negate F (C3.multiply F a b))
  ≡⟨ C3.negateInvolutive F (C3.multiply F a b) ⟩
    C3.multiply F a b
  ∎

realInterchange :
  ∀ {r} (F : C3.RealField r)
    (a b c d : C3.Carrier F) →
  C3.add F (C3.add F a b) (C3.add F c d)
  ≡
  C3.add F (C3.add F a c) (C3.add F b d)
realInterchange F a b c d =
  begin
    C3.add F (C3.add F a b) (C3.add F c d)
  ≡⟨ C3.addAssociative F a b (C3.add F c d) ⟩
    C3.add F a (C3.add F b (C3.add F c d))
  ≡⟨ cong (C3.add F a)
      (sym (C3.addAssociative F b c d)) ⟩
    C3.add F a (C3.add F (C3.add F b c) d)
  ≡⟨ cong (C3.add F a)
      (cong (λ value → C3.add F value d)
        (C3.addCommutative F b c)) ⟩
    C3.add F a (C3.add F (C3.add F c b) d)
  ≡⟨ cong (C3.add F a)
      (C3.addAssociative F c b d) ⟩
    C3.add F a (C3.add F c (C3.add F b d))
  ≡⟨ sym (C3.addAssociative F a c (C3.add F b d)) ⟩
    C3.add F (C3.add F a c) (C3.add F b d)
  ∎

------------------------------------------------------------------------
-- Complex and C3 algebra.
------------------------------------------------------------------------

complexAddAssociative :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex F) →
  C3.complexAdd (C3.complexAdd a b) c
  ≡ C3.complexAdd a (C3.complexAdd b c)
complexAddAssociative {F = F}
  (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci)
  rewrite C3.addAssociative F ar br cr
        | C3.addAssociative F ai bi ci = refl

complexAddCommutative :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) →
  C3.complexAdd a b ≡ C3.complexAdd b a
complexAddCommutative {F = F}
  (C3.complex ar ai) (C3.complex br bi)
  rewrite C3.addCommutative F ar br
        | C3.addCommutative F ai bi = refl

complexAddZeroLeft :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Complex F) →
  C3.complexAdd (C3.complexZero F) a ≡ a
complexAddZeroLeft {F = F} (C3.complex ar ai)
  rewrite C3.addZeroLeft F ar
        | C3.addZeroLeft F ai = refl

complexAddZeroRight :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Complex F) →
  C3.complexAdd a (C3.complexZero F) ≡ a
complexAddZeroRight {F = F} (C3.complex ar ai)
  rewrite realAddZeroRight F ar
        | realAddZeroRight F ai = refl

complexMultiplyCommutative :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) →
  C3.complexMultiply a b ≡ C3.complexMultiply b a
complexMultiplyCommutative {F = F}
  (C3.complex ar ai) (C3.complex br bi) =
  cong₂ C3.complex
    (cong₂ (C3.add F)
      (C3.multiplyCommutative F ar br)
      (cong (C3.negate F) (C3.multiplyCommutative F ai bi)))
    (begin
      C3.add F
        (C3.multiply F ar bi)
        (C3.multiply F ai br)
    ≡⟨ cong₂ (C3.add F)
        (C3.multiplyCommutative F ar bi)
        (C3.multiplyCommutative F ai br) ⟩
      C3.add F
        (C3.multiply F bi ar)
        (C3.multiply F br ai)
    ≡⟨ C3.addCommutative F
        (C3.multiply F bi ar)
        (C3.multiply F br ai) ⟩
      C3.add F
        (C3.multiply F br ai)
        (C3.multiply F bi ar)
    ∎)

complexMultiplyDistributesLeft :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex F) →
  C3.complexMultiply a (C3.complexAdd b c)
  ≡
  C3.complexAdd
    (C3.complexMultiply a b)
    (C3.complexMultiply a c)
complexMultiplyDistributesLeft {F = F}
  (C3.complex ar ai)
  (C3.complex br bi)
  (C3.complex cr ci) =
  cong₂ C3.complex realCoordinate imaginaryCoordinate
  where
    realCoordinate :
      C3.add F
        (C3.multiply F ar (C3.add F br cr))
        (C3.negate F
          (C3.multiply F ai (C3.add F bi ci)))
      ≡
      C3.add F
        (C3.add F
          (C3.multiply F ar br)
          (C3.negate F (C3.multiply F ai bi)))
        (C3.add F
          (C3.multiply F ar cr)
          (C3.negate F (C3.multiply F ai ci)))
    realCoordinate =
      begin
        C3.add F
          (C3.multiply F ar (C3.add F br cr))
          (C3.negate F
            (C3.multiply F ai (C3.add F bi ci)))
      ≡⟨ cong₂ (C3.add F)
          (C3.distributeLeft F ar br cr)
          (cong (C3.negate F)
            (C3.distributeLeft F ai bi ci)) ⟩
        C3.add F
          (C3.add F
            (C3.multiply F ar br)
            (C3.multiply F ar cr))
          (C3.negate F
            (C3.add F
              (C3.multiply F ai bi)
              (C3.multiply F ai ci)))
      ≡⟨ cong (C3.add F
          (C3.add F
            (C3.multiply F ar br)
            (C3.multiply F ar cr)))
          (realNegateAdd F
            (C3.multiply F ai bi)
            (C3.multiply F ai ci)) ⟩
        C3.add F
          (C3.add F
            (C3.multiply F ar br)
            (C3.multiply F ar cr))
          (C3.add F
            (C3.negate F (C3.multiply F ai bi))
            (C3.negate F (C3.multiply F ai ci)))
      ≡⟨ realInterchange F
          (C3.multiply F ar br)
          (C3.multiply F ar cr)
          (C3.negate F (C3.multiply F ai bi))
          (C3.negate F (C3.multiply F ai ci)) ⟩
        C3.add F
          (C3.add F
            (C3.multiply F ar br)
            (C3.negate F (C3.multiply F ai bi)))
          (C3.add F
            (C3.multiply F ar cr)
            (C3.negate F (C3.multiply F ai ci)))
      ∎

    imaginaryCoordinate :
      C3.add F
        (C3.multiply F ar (C3.add F bi ci))
        (C3.multiply F ai (C3.add F br cr))
      ≡
      C3.add F
        (C3.add F
          (C3.multiply F ar bi)
          (C3.multiply F ai br))
        (C3.add F
          (C3.multiply F ar ci)
          (C3.multiply F ai cr))
    imaginaryCoordinate =
      begin
        C3.add F
          (C3.multiply F ar (C3.add F bi ci))
          (C3.multiply F ai (C3.add F br cr))
      ≡⟨ cong₂ (C3.add F)
          (C3.distributeLeft F ar bi ci)
          (C3.distributeLeft F ai br cr) ⟩
        C3.add F
          (C3.add F
            (C3.multiply F ar bi)
            (C3.multiply F ar ci))
          (C3.add F
            (C3.multiply F ai br)
            (C3.multiply F ai cr))
      ≡⟨ realInterchange F
          (C3.multiply F ar bi)
          (C3.multiply F ar ci)
          (C3.multiply F ai br)
          (C3.multiply F ai cr) ⟩
        C3.add F
          (C3.add F
            (C3.multiply F ar bi)
            (C3.multiply F ai br))
          (C3.add F
            (C3.multiply F ar ci)
            (C3.multiply F ai cr))
      ∎

complexMultiplyDistributesRight :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex F) →
  C3.complexMultiply (C3.complexAdd a b) c
  ≡
  C3.complexAdd
    (C3.complexMultiply a c)
    (C3.complexMultiply b c)
complexMultiplyDistributesRight a b c =
  begin
    C3.complexMultiply (C3.complexAdd a b) c
  ≡⟨ complexMultiplyCommutative (C3.complexAdd a b) c ⟩
    C3.complexMultiply c (C3.complexAdd a b)
  ≡⟨ complexMultiplyDistributesLeft c a b ⟩
    C3.complexAdd
      (C3.complexMultiply c a)
      (C3.complexMultiply c b)
  ≡⟨ cong₂ C3.complexAdd
      (complexMultiplyCommutative c a)
      (complexMultiplyCommutative c b) ⟩
    C3.complexAdd
      (C3.complexMultiply a c)
      (C3.complexMultiply b c)
  ∎

complexInterchange :
  ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex F) →
  C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d)
  ≡
  C3.complexAdd (C3.complexAdd a c) (C3.complexAdd b d)
complexInterchange a b c d =
  begin
    C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d)
  ≡⟨ complexAddAssociative a b (C3.complexAdd c d) ⟩
    C3.complexAdd a (C3.complexAdd b (C3.complexAdd c d))
  ≡⟨ cong (C3.complexAdd a)
      (sym (complexAddAssociative b c d)) ⟩
    C3.complexAdd a (C3.complexAdd (C3.complexAdd b c) d)
  ≡⟨ cong (C3.complexAdd a)
      (cong (λ value → C3.complexAdd value d)
        (complexAddCommutative b c)) ⟩
    C3.complexAdd a (C3.complexAdd (C3.complexAdd c b) d)
  ≡⟨ cong (C3.complexAdd a)
      (complexAddAssociative c b d) ⟩
    C3.complexAdd a (C3.complexAdd c (C3.complexAdd b d))
  ≡⟨ sym (complexAddAssociative a c (C3.complexAdd b d)) ⟩
    C3.complexAdd (C3.complexAdd a c) (C3.complexAdd b d)
  ∎

complexThreePairInterchange :
  ∀ {r} {F : C3.RealField r}
    (a b c d e f : C3.Complex F) →
  C3.complexAdd
    (C3.complexAdd
      (C3.complexAdd a d)
      (C3.complexAdd b e))
    (C3.complexAdd c f)
  ≡
  C3.complexAdd
    (C3.complexAdd (C3.complexAdd a b) c)
    (C3.complexAdd (C3.complexAdd d e) f)
complexThreePairInterchange a b c d e f =
  begin
    C3.complexAdd
      (C3.complexAdd
        (C3.complexAdd a d)
        (C3.complexAdd b e))
      (C3.complexAdd c f)
  ≡⟨ cong (λ value → C3.complexAdd value (C3.complexAdd c f))
      (complexInterchange a d b e) ⟩
    C3.complexAdd
      (C3.complexAdd
        (C3.complexAdd a b)
        (C3.complexAdd d e))
      (C3.complexAdd c f)
  ≡⟨ complexInterchange
      (C3.complexAdd a b)
      (C3.complexAdd d e)
      c f ⟩
    C3.complexAdd
      (C3.complexAdd (C3.complexAdd a b) c)
      (C3.complexAdd (C3.complexAdd d e) f)
  ∎

bilinearDot3RightAdd :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  C3.bilinearDot3 u (C3.complex3Add v w)
  ≡
  C3.complexAdd
    (C3.bilinearDot3 u v)
    (C3.bilinearDot3 u w)
bilinearDot3RightAdd
  (C3.complex3 ux uy uz)
  (C3.complex3 vx vy vz)
  (C3.complex3 wx wy wz)
  rewrite complexMultiplyDistributesLeft ux vx wx
        | complexMultiplyDistributesLeft uy vy wy
        | complexMultiplyDistributesLeft uz vz wz =
  complexThreePairInterchange
    (C3.complexMultiply ux vx)
    (C3.complexMultiply uy vy)
    (C3.complexMultiply uz vz)
    (C3.complexMultiply ux wx)
    (C3.complexMultiply uy wy)
    (C3.complexMultiply uz wz)

bilinearDot3Commutative :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.bilinearDot3 u v ≡ C3.bilinearDot3 v u
bilinearDot3Commutative
  (C3.complex3 ux uy uz)
  (C3.complex3 vx vy vz)
  rewrite complexMultiplyCommutative ux vx
        | complexMultiplyCommutative uy vy
        | complexMultiplyCommutative uz vz = refl

realEmbedAdd :
  ∀ {r} (F : C3.RealField r)
    (a b : C3.Carrier F) →
  C3.realEmbed F (C3.add F a b)
  ≡
  C3.complexAdd (C3.realEmbed F a) (C3.realEmbed F b)
realEmbedAdd F a b
  rewrite C3.addZeroLeft F (C3.zero F) = refl

modeVectorAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (p q : Z3.FourierMode) →
  C3.modeVector E (Z3.addMode p q)
  ≡
  C3.complex3Add (C3.modeVector E p) (C3.modeVector E q)
modeVectorAdd {F = F} E
  (Z3.mode px py pz)
  (Z3.mode qx qy qz)
  rewrite C3.embedAdd E px qx
        | C3.embedAdd E py qy
        | C3.embedAdd E pz qz
        | realEmbedAdd F (C3.embedInteger E px) (C3.embedInteger E qx)
        | realEmbedAdd F (C3.embedInteger E py) (C3.embedInteger E qy)
        | realEmbedAdd F (C3.embedInteger E pz) (C3.embedInteger E qz) = refl

complex3AlgebraLawsClosed : Bool
complex3AlgebraLawsClosed = true

complex3AlgebraLawsClosedIsTrue :
  complex3AlgebraLawsClosed ≡ true
complex3AlgebraLawsClosedIsTrue = refl
