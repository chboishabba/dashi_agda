module DASHI.Analysis.StoichiometricConservationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Analysis.StoichiometricConservation

unitAdditive : AdditiveQuantity ⊤
unitAdditive = record
  { zero = tt
  ; _⊕_ = λ _ _ → tt
  ; rightIdentity = λ _ → refl
  }

unitStoichiometricSystem :
  StoichiometricSystem ⊤ ⊤ ⊤ ⊤
unitStoichiometricSystem = record
  { additive = unitAdditive
  ; stoichiometricColumn = λ _ → tt
  ; leftFunctional = λ _ → tt
  ; quantity = λ _ → tt
  ; step = λ _ _ → tt
  ; quantityUpdate = λ _ _ → refl
  }

unitLeftKernel :
  LeftKernelConservation unitStoichiometricSystem
unitLeftKernel = record
  { annihilatesStoichiometry = λ _ → refl
  }

unitTwoReactionPath :
  Agda.Builtin.List.List ⊤
unitTwoReactionPath = tt ∷ tt ∷ []

unitStepConserves :
  quantity unitStoichiometricSystem
    (step unitStoichiometricSystem tt tt)
    ≡ quantity unitStoichiometricSystem tt
unitStepConserves =
  reactionStepConserves
    unitStoichiometricSystem
    unitLeftKernel
    tt
    tt

unitPathConserves :
  quantity unitStoichiometricSystem
    (runReactionPath unitStoichiometricSystem unitTwoReactionPath tt)
    ≡ quantity unitStoichiometricSystem tt
unitPathConserves =
  reactionPathConserves
    unitStoichiometricSystem
    unitLeftKernel
    unitTwoReactionPath
    tt
