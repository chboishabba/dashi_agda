{-# OPTIONS --safe #-}
module DASHI.Core.TritCPRMultiscaleInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv; inv-invol)
open import DASHI.Core.MultiscaleMDL

------------------------------------------------------------------------
-- Concrete nested ternary C/P/R hierarchy.
--
-- A successor state stores one new fine trit beside the entire previous-scale
-- state.  Projection forgets exactly that new trit, lift inserts the neutral
-- trit, residual records the forgotten trit, and reconstruction is exact.

TritTower : Nat → Set
TritTower zero = Trit
TritTower (suc j) = Trit × TritTower j

tritProject : ∀ {j} → TritTower (suc j) → TritTower j
tritProject = proj₂

tritLift : ∀ {j} → TritTower j → TritTower (suc j)
tritLift x = zer , x

trit-project-lift : ∀ {j} (x : TritTower j) → tritProject (tritLift x) ≡ x
trit-project-lift x = refl

tritMultiscaleCarrier : MultiscaleCarrier
tritMultiscaleCarrier =
  record
    { Carrier = TritTower
    ; project = tritProject
    ; lift = tritLift
    ; project-lift = trit-project-lift
    }

tritResidual : ∀ {j} → TritTower (suc j) → Trit
tritResidual = proj₁

tritReconstruct : ∀ {j} → TritTower j → Trit → TritTower (suc j)
tritReconstruct coarse remainder = remainder , coarse

trit-reconstruct-project-residual :
  ∀ {j} (x : TritTower (suc j)) →
  tritReconstruct (tritProject x) (tritResidual x) ≡ x
trit-reconstruct-project-residual (remainder , coarse) = refl

tritResidualCodec : ResidualCodec tritMultiscaleCarrier
tritResidualCodec =
  record
    { Residual = λ _ → Trit
    ; residual = tritResidual
    ; reconstruct = tritReconstruct
    ; reconstruct-project-residual = trit-reconstruct-project-residual
    }

trit-join-split :
  ∀ {j} (x : TritTower (suc j)) →
  join tritResidualCodec (split tritResidualCodec x) ≡ x
trit-join-split x = join-split tritResidualCodec x

------------------------------------------------------------------------
-- Concrete inversion action at every rank.

invertTower : ∀ {j} → TritTower j → TritTower j
invertTower {zero} t = inv t
invertTower {suc j} (t , xs) = inv t , invertTower xs

invertTower-invol : ∀ {j} (x : TritTower j) → invertTower (invertTower x) ≡ x
invertTower-invol {zero} t = inv-invol t
invertTower-invol {suc j} (t , xs) rewrite inv-invol t | invertTower-invol xs = refl

tritIdentityKernelTower : KernelTower tritMultiscaleCarrier
tritIdentityKernelTower =
  record
    { kernel = λ _ x → x
    ; project-kernel = λ _ → refl
    }

data TritSymmetry : Set where
  identitySymmetry inversionSymmetry : TritSymmetry

tritAct : ∀ {j} → TritSymmetry → TritTower j → TritTower j
tritAct identitySymmetry x = x
tritAct inversionSymmetry x = invertTower x

tritSymmetryAction : SymmetryAction tritMultiscaleCarrier
tritSymmetryAction =
  record
    { Symmetry = λ _ → TritSymmetry
    ; identity = identitySymmetry
    ; act = tritAct
    ; identity-act = λ _ → refl
    }
