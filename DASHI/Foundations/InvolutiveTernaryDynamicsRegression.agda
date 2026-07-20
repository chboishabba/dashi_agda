module DASHI.Foundations.InvolutiveTernaryDynamicsRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Algebra.Trit as Trit
open import DASHI.Foundations.InvolutiveTernaryDynamics
open import DASHI.Foundations.InvolutiveTernaryRenormalisation

------------------------------------------------------------------------
-- Concrete ternary cancellation dynamics.
--
-- Equal active signs persist, opposite signs cancel to zero, and zero passes
-- through the incoming control.  This is a finite witness that the generic
-- contracts are inhabited; it is not promoted as a universal application
-- rule.

cancel : Trit.Trit → Trit.Trit → Trit.Trit
cancel Trit.neg Trit.neg = Trit.neg
cancel Trit.neg Trit.zer = Trit.neg
cancel Trit.neg Trit.pos = Trit.zer
cancel Trit.zer u = u
cancel Trit.pos Trit.neg = Trit.zer
cancel Trit.pos Trit.zer = Trit.pos
cancel Trit.pos Trit.pos = Trit.pos

cancel-equivariant :
  ∀ s u →
  cancel (Trit.inv s) (Trit.inv u) ≡ Trit.inv (cancel s u)
cancel-equivariant Trit.neg Trit.neg = refl
cancel-equivariant Trit.neg Trit.zer = refl
cancel-equivariant Trit.neg Trit.pos = refl
cancel-equivariant Trit.zer Trit.neg = refl
cancel-equivariant Trit.zer Trit.zer = refl
cancel-equivariant Trit.zer Trit.pos = refl
cancel-equivariant Trit.pos Trit.neg = refl
cancel-equivariant Trit.pos Trit.zer = refl
cancel-equivariant Trit.pos Trit.pos = refl

cancellationDynamics : InvolutiveDynamics
cancellationDynamics = record
  { State = Trit.Trit
  ; Control = Trit.Trit
  ; stateι = Trit.inv
  ; controlι = Trit.inv
  ; stateι-involutive = Trit.inv-invol
  ; controlι-involutive = Trit.inv-invol
  ; step = cancel
  ; step-equivariant = cancel-equivariant
  }

------------------------------------------------------------------------
-- Symmetry action: zero has cost 0 and either active orientation has cost 1.

tritAction : Trit.Trit → Nat
tritAction Trit.neg = suc zero
tritAction Trit.zer = zero
tritAction Trit.pos = suc zero

tritAction-even : ∀ s → tritAction (Trit.inv s) ≡ tritAction s
tritAction-even Trit.neg = refl
tritAction-even Trit.zer = refl
tritAction-even Trit.pos = refl

zero-minimal : ∀ s → tritAction Trit.zer ≤ tritAction s
zero-minimal Trit.neg = z≤n
zero-minimal Trit.zer = z≤n
zero-minimal Trit.pos = z≤n

cancellationAction : EvenAction cancellationDynamics
cancellationAction = record
  { action = tritAction
  ; action-even = tritAction-even
  ; neutral = Trit.zer
  ; neutral-fixed-by-involution = refl
  ; neutral-minimal = zero-minimal
  }

zeroEigenstate : FixedPoint cancellationDynamics Trit.zer
zeroEigenstate = Trit.zer , refl

negativePersistent : cancel Trit.neg Trit.neg ≡ Trit.neg
negativePersistent = refl

positivePersistent : cancel Trit.pos Trit.pos ≡ Trit.pos
positivePersistent = refl

oppositesCancelLeft : cancel Trit.neg Trit.pos ≡ Trit.zer
oppositesCancelLeft = refl

oppositesCancelRight : cancel Trit.pos Trit.neg ≡ Trit.zer
oppositesCancelRight = refl

------------------------------------------------------------------------
-- Identity coarse tower as the minimal commuting witness.
--
-- Application modules can replace this with 3-to-1 blocking, recognisable
-- substitution, p-adic prefix truncation, or another concrete lift while
-- reusing the same contracts.

identityTritTower : InvolutiveScaleTower
identityTritTower = record
  { Carrier = λ _ → Trit.Trit
  ; ι = λ _ → Trit.inv
  ; ι-involutive = λ _ → Trit.inv-invol
  ; coarse = λ _ s → s
  ; coarse-equivariant = λ _ _ → refl
  }

identityLiftedDynamics : LiftedInvolutiveDynamics identityTritTower
identityLiftedDynamics = record
  { Control = λ _ → Trit.Trit
  ; controlι = λ _ → Trit.inv
  ; controlι-involutive = λ _ → Trit.inv-invol
  ; liftControl = λ _ u → u
  ; liftControl-equivariant = λ _ _ → refl
  ; step = λ _ → cancel
  ; step-equivariant = λ _ → cancel-equivariant
  ; coarse-step-commutes = λ _ _ _ → refl
  }

identityRecognisable :
  ∀ j →
  RecognisableScaleStep identityTritTower j
identityRecognisable j = record
  { refine = λ macro → macro
  ; coarse-refine = λ _ → refl
  }

------------------------------------------------------------------------
-- Regression bundle.

record InvolutiveTernaryRegressionReceipt : Set where
  constructor receipt
  field
    involutionIsLiteral : ∀ t → Trit.inv (Trit.inv t) ≡ t
    cancellationIsEquivariant :
      ∀ s u →
      cancel (Trit.inv s) (Trit.inv u) ≡ Trit.inv (cancel s u)
    neutralIsEigenstate : FixedPoint cancellationDynamics Trit.zer
    oppositeOrientationsCancel : cancel Trit.neg Trit.pos ≡ Trit.zer
    coarseDynamicsCommutes :
      ∀ j s u →
      coarse identityTritTower j (step identityLiftedDynamics j s u) ≡
      step identityLiftedDynamics (suc j)
        (coarse identityTritTower j s)
        (liftControl identityLiftedDynamics j u)

canonicalRegressionReceipt : InvolutiveTernaryRegressionReceipt
canonicalRegressionReceipt = receipt
  Trit.inv-invol
  cancel-equivariant
  zeroEigenstate
  refl
  (λ _ _ _ → refl)
