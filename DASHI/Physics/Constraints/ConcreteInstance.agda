module DASHI.Physics.Constraints.ConcreteInstance where

open import Data.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket
open import DASHI.Physics.Constraints.Closure

-- A concrete, small constraint system with three generators.
data C : Set where
  CR : C
  CP : C
  CC : C

CS : ConstraintSystem
CS =
  record
    { Constraint = C
    ; actsOn = λ S → S
    ; apply = λ {S} _ x → x
    }

L : LieLike CS
L =
  record
    { _[_,]_ = bracket
    ; antisym = ⊤
    ; jacobi = ⊤
    }
  where
    bracket : C → C → C
    bracket CR CP = CC
    bracket CP CR = CC
    bracket CP CC = CR
    bracket CC CP = CR
    bracket CR CC = CP
    bracket CC CR = CP
    bracket CR CR = CR
    bracket CP CP = CP
    bracket CC CC = CC

closure : ClosureLaw CS L
closure =
  record
    { closes = λ c₁ c₂ → (LieLike._[_,]_ L c₁ c₂ , refl)
    }
