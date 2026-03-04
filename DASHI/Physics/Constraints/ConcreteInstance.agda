module DASHI.Physics.Constraints.ConcreteInstance where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket
open import DASHI.Physics.Constraints.Closure

-- A concrete, minimal constraint system with a single constraint.
CS : ConstraintSystem
CS =
  record
    { Constraint = ⊤
    ; actsOn = λ S → S
    ; apply = λ {S} _ x → x
    }

L : LieLike CS
L =
  record
    { _[_,]_ = λ _ _ → tt
    ; antisym = ⊤
    ; jacobi = ⊤
    }

closure : ClosureLaw CS L
closure =
  record
    { closes = λ _ _ → (tt , refl)
    }
