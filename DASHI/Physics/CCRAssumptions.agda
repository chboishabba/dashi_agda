module DASHI.Physics.CCRAssumptions where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (⊤)

record OperatorAlgebra : Set₁ where
  field
    Op : Set
    I  : Op
    _+_ _*_ : Op → Op → Op
    [_,_] : Op → Op → Op
    Scalar : Set
    s∙ : Scalar → Op

record CCRGate (A : OperatorAlgebra) : Set₁ where
  open OperatorAlgebra A
  field
    D R : Op
    ħ  : Scalar
    continuum-limit : ⊤
    CCR : [ D , R ] ≡ s∙ ħ
