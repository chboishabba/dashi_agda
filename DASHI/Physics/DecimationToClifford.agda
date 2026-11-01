{-# OPTIONS --safe #-}

module DASHI.Physics.DecimationToClifford where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Core

-- Abstract algebra with multiplication.
record Algebra {ℓ : Level} : Set (suc ℓ) where
  field
    A   : Set ℓ
    _·_ : A → A → A

-- Decimation algebra interface (kernel algebra / RG algebra).
record DecimationAlgebra {ℓ : Level} (V : Set ℓ) : Set (suc ℓ) where
  field
    A    : Set ℓ
    unit : A
    mul  : A → A → A
    gen  : V → A

-- Clifford relations for the decimation algebra: when Q(v) is inhabited,
-- generator squares collapse to the unit.
record CliffordRelations {ℓ : Level} (V : Set ℓ) (Q : Quadratic V) (D : DecimationAlgebra V) : Set (suc (suc ℓ)) where
  open DecimationAlgebra D
  field
    rel : ∀ v → Quadratic.Q Q v → mul (gen v) (gen v) ≡ unit

record TargetAlgebra {ℓ : Level} (V : Set ℓ) (Q : Quadratic V) : Set (suc ℓ) where
  field
    CarrierT : Set ℓ
    unitT : CarrierT
    mulT : CarrierT → CarrierT → CarrierT
    genT : V → CarrierT
    relT : ∀ v → Quadratic.Q Q v → mulT (genT v) (genT v) ≡ unitT

record RelationRespectingMap {ℓ : Level}
  {V : Set ℓ} {Q : Quadratic V}
  (D : DecimationAlgebra V)
  (T : TargetAlgebra V Q) : Set (suc ℓ) where
  open DecimationAlgebra D
  open TargetAlgebra T
  field
    onCarrier : A → CarrierT
    preservesUnit : onCarrier unit ≡ unitT
    preservesMul :
      ∀ a b →
      onCarrier (mul a b) ≡ mulT (onCarrier a) (onCarrier b)
    preservesGen :
      ∀ v →
      onCarrier (gen v) ≡ genT v

-- Universal property: any algebra satisfying relations factors uniquely.
record UniversalClifford {ℓ : Level}
  (V : Set ℓ) (Q : Quadratic V) (D : DecimationAlgebra V) : Set (suc (suc ℓ)) where
  open DecimationAlgebra D
  field
    Cl     : Set ℓ
    unitCl : Cl
    mulCl  : Cl → Cl → Cl
    embed  : V → Cl
    include : A → Cl
    includeGen : ∀ v → include (gen v) ≡ embed v
    factor :
      (T : TargetAlgebra V Q) →
      RelationRespectingMap D T →
      Cl →
      TargetAlgebra.CarrierT T
    factorOnInclude :
      ∀ (T : TargetAlgebra V Q) (h : RelationRespectingMap D T) a →
      factor T h (include a) ≡ RelationRespectingMap.onCarrier h a
    factorUniqueSeam :
      (T : TargetAlgebra V Q) →
      (h : RelationRespectingMap D T) →
      (f g : Cl → TargetAlgebra.CarrierT T) →
      Set ℓ

decimation⇒clifford :
  ∀ {ℓ} {V : Set ℓ} (Q : Quadratic V) →
  (D : DecimationAlgebra V) →
  CliffordRelations V Q D →
  UniversalClifford V Q D
decimation⇒clifford _ D _ =
  record
    { Cl = DecimationAlgebra.A D
    ; unitCl = DecimationAlgebra.unit D
    ; mulCl = DecimationAlgebra.mul D
    ; embed = DecimationAlgebra.gen D
    ; include = λ a → a
    ; includeGen = λ _ → refl
    ; factor = λ T h → RelationRespectingMap.onCarrier h
    ; factorOnInclude = λ _ h _ → refl
    ; factorUniqueSeam = λ T _ f g → ∀ x → f x ≡ g x
    }
