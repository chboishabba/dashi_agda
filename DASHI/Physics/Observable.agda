module DASHI.Physics.Observable where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.SymmetryQuotient as SQ

record ObservableTheory {ℓ : Level}
  (Q : SQ.QuotientedTheory ℓ) : Set (lsuc ℓ) where
  field
    Observable : Set ℓ
    Value      : Observable → Set ℓ

    eval : (O : Observable) → SQ.PhysState Q → Value O

record ObservableAlgebra {ℓ : Level}
  (Q : SQ.QuotientedTheory ℓ) : Set (lsuc ℓ) where
  field
    Observable : Set ℓ
    Scalar     : Set ℓ

    _+O_ : Observable → Observable → Observable
    _·O_ : Scalar → Observable → Observable
    _*O_ : Observable → Observable → Observable

record SymmetryInvariantObservables {ℓ : Level}
  (Q : SQ.QuotientedTheory ℓ)
  (Obs : ObservableTheory Q) : Set (lsuc ℓ) where
  field
    eval-well-defined :
      ∀ O x y →
      SQ.classOf Q x ≡ SQ.classOf Q y →
      ObservableTheory.eval Obs O (SQ.classOf Q x)
        ≡ ObservableTheory.eval Obs O (SQ.classOf Q y)
