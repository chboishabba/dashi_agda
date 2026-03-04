module DASHI.Metric.TernaryUltrametric where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Ultrametric

open import DASHI.Algebra.BalancedTernary using (Trit; neg; zero; pos)

-- Discrete ultrametric on Trit (honest, non-postulated).
-- d x y = 0 if x ≡ y, else 1.
dT : Trit → Trit → Nat
dT neg  neg  = 0
dT zero zero = 0
dT pos  pos  = 0
dT _    _    = suc zero

id-zeroT : ∀ x → dT x x ≡ 0
id-zeroT neg  = refl
id-zeroT zero = refl
id-zeroT pos  = refl

symT : ∀ x y → dT x y ≡ dT y x
symT neg  neg  = refl
symT neg  zero = refl
symT neg  pos  = refl
symT zero neg  = refl
symT zero zero = refl
symT zero pos  = refl
symT pos  neg  = refl
symT pos  zero = refl
symT pos  pos  = refl

-- For discrete metric: if x=z then 0 ≤ max; otherwise 1 ≤ max (since at least
-- one of x≠y or y≠z holds).
ultraT : ∀ x y z → dT x z ≤ max (dT x y) (dT y z)
ultraT neg  neg  neg  = z≤n
ultraT neg  neg  zero = s≤s z≤n
ultraT neg  neg  pos  = s≤s z≤n
ultraT neg  zero neg  = z≤n
ultraT neg  zero zero = s≤s z≤n
ultraT neg  zero pos  = s≤s z≤n
ultraT neg  pos  neg  = z≤n
ultraT neg  pos  zero = s≤s z≤n
ultraT neg  pos  pos  = s≤s z≤n
ultraT zero neg  neg  = s≤s z≤n
ultraT zero neg  zero = z≤n
ultraT zero neg  pos  = s≤s z≤n
ultraT zero zero neg  = s≤s z≤n
ultraT zero zero zero = z≤n
ultraT zero zero pos  = s≤s z≤n
ultraT zero pos  neg  = s≤s z≤n
ultraT zero pos  zero = z≤n
ultraT zero pos  pos  = s≤s z≤n
ultraT pos  neg  neg  = s≤s z≤n
ultraT pos  neg  zero = s≤s z≤n
ultraT pos  neg  pos  = z≤n
ultraT pos  zero neg  = s≤s z≤n
ultraT pos  zero zero = s≤s z≤n
ultraT pos  zero pos  = z≤n
ultraT pos  pos  neg  = s≤s z≤n
ultraT pos  pos  zero = s≤s z≤n
ultraT pos  pos  pos  = z≤n

S : Set
S = Trit

U : Ultrametric S
U = record
  { d             = dT
  ; id-zero       = id-zeroT
  ; symmetric     = symT
  ; ultratriangle = ultraT
  }
