module DASHI.Physics.DefaultClosure where

open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _<_; _⊔_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)

open import Ultrametric as UMetric
open import Contraction as Contraction using (Contractive≢; StrictContraction)
open import DASHI.Combinatorics.Entropy using (Involution)
import DASHI.Physics.ClosureGlue as Glue
open import DASHI.Physics.ClosureStatusFromGlue
open import DASHI.Physics.UnificationClosure

------------------------------------------------------------------------
-- A concrete, total instance to close the physics glue
------------------------------------------------------------------------

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Carrier : Set
Carrier = Bool

-- Discrete ultrametric on Bool: 0 if equal, 1 otherwise.
dBool : Carrier → Carrier → Nat
dBool true  true  = zero
dBool false false = zero
dBool true  false = suc zero
dBool false true  = suc zero

id-zeroBool : ∀ x → dBool x x ≡ 0
id-zeroBool true  = refl
id-zeroBool false = refl

symBool : ∀ x y → dBool x y ≡ dBool y x
symBool true  true  = refl
symBool false false = refl
symBool true  false = refl
symBool false true  = refl

ultratriangleBool : ∀ x y z → dBool x z ≤ (dBool x y ⊔ dBool y z)
ultratriangleBool true  true  true  = z≤n
ultratriangleBool true  true  false = s≤s z≤n
ultratriangleBool true  false true  = z≤n
ultratriangleBool true  false false = s≤s z≤n
ultratriangleBool false true  true  = s≤s z≤n
ultratriangleBool false true  false = z≤n
ultratriangleBool false false true  = s≤s z≤n
ultratriangleBool false false false = z≤n

boolUltrametric : UMetric.Ultrametric Carrier
boolUltrametric =
  record
    { d = dBool
    ; id-zero = id-zeroBool
    ; symmetric = symBool
    ; ultratriangle = ultratriangleBool
    }

-- Constant contraction to false.
T : Carrier → Carrier
T _ = false

contractiveBool-proof : ∀ x y → x ≢ y → dBool (T x) (T y) < dBool x y
contractiveBool-proof true  false _   = s≤s z≤n
contractiveBool-proof false true  _   = s≤s z≤n
contractiveBool-proof true  true  x≢y = ⊥-elim (x≢y refl)
contractiveBool-proof false false x≢y = ⊥-elim (x≢y refl)

contractiveBool : Contraction.Contractive≢ boolUltrametric T
contractiveBool =
  record
    { contraction≢ = λ {x} {y} x≢y →
        contractiveBool-proof x y x≢y
    }

boolTrueNeqFalse : false ≡ true → ⊥
boolTrueNeqFalse ()

uniqueBool : ∀ x → T x ≡ x → x ≡ false
uniqueBool true  hx = ⊥-elim (boolTrueNeqFalse hx)
uniqueBool false _  = refl

strictBool : Contraction.StrictContraction boolUltrametric T
strictBool =
  record
    { contractive≢ = contractiveBool
    ; fp = false
    ; fixed = refl
    ; unique = uniqueBool
    }

invBool : Involution Carrier
invBool = record
  { ι = λ x → x
  ; invol = λ _ → refl
  }

defaultClosure : Glue.ClosureAxioms
defaultClosure = Glue.mkDefaultClosure boolUltrametric T strictBool invBool

defaultClosureStatus : ClosureStatus
defaultClosureStatus = closureStatusFromGlue defaultClosure
