module DASHI.Physics.Toy.ScalarControlledNoncommutation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Vec using ([]; _∷_)

open import DASHI.Algebra.Trit using (zer)
import DASHI.Algebra.Trit as T
open import DASHI.Physics.Toy.ScalarContinuum

projectAfterStep :
  (n : Nat) → Carrier (suc n) → Carrier n
projectAfterStep n x = dropLast (scalarStep (suc n) x)

stepAfterProject :
  (n : Nat) → Carrier (suc n) → Carrier n
stepAfterProject n x = scalarStep n (dropLast x)

controlled-commutation-defect :
  ∀ n (x : Carrier (suc n)) →
  TailApprox (projectAfterStep n x) (stepAfterProject n x)
controlled-commutation-defect n x = dropLast-relaxSym≈-with zer x

noncommutingInput : Carrier (suc (suc zero))
noncommutingInput = T.pos ∷ T.pos ∷ T.pos ∷ []

projectAfterStep-witness :
  projectAfterStep (suc zero) noncommutingInput
  ≡
  zer ∷ T.pos ∷ []
projectAfterStep-witness = refl

stepAfterProject-witness :
  stepAfterProject (suc zero) noncommutingInput
  ≡
  zer ∷ zer ∷ []
stepAfterProject-witness = refl

scalar-project-step-noncommutes :
  projectAfterStep (suc zero) noncommutingInput
  ≡
  stepAfterProject (suc zero) noncommutingInput
  →
  ⊥
scalar-project-step-noncommutes ()

record ControlledNoncommutationReceipt : Set where
  field
    controlledAtEveryScale :
      ∀ n (x : Carrier (suc n)) →
      TailApprox (projectAfterStep n x) (stepAfterProject n x)

    nontrivialAtFiniteScale :
      projectAfterStep (suc zero) noncommutingInput
      ≡
      stepAfterProject (suc zero) noncommutingInput
      →
      ⊥

scalarControlledNoncommutation : ControlledNoncommutationReceipt
scalarControlledNoncommutation =
  record
    { controlledAtEveryScale = controlled-commutation-defect
    ; nontrivialAtFiniteScale = scalar-project-step-noncommutes
    }

controlledNoncommutationHarness :
  TailApprox
    (projectAfterStep (suc zero) noncommutingInput)
    (stepAfterProject (suc zero) noncommutingInput)
  ×
  (projectAfterStep (suc zero) noncommutingInput
   ≡ stepAfterProject (suc zero) noncommutingInput
   → ⊥)
controlledNoncommutationHarness =
  controlled-commutation-defect (suc zero) noncommutingInput
  , scalar-project-step-noncommutes
