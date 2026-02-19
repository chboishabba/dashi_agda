module DASHI.Combinatorics.PDA_MDL.KernelSelection where

open import DASHI.Combinatorics.PDA_MDL.Prelude
open import DASHI.Combinatorics.PDA_MDL.PDA

------------------------------------------------------------------------
-- Generic kernel family

record KernelFamily (I S : Set) : Set₁ where
  field
    K : I → S → S
    Lkernel : I → CodeLength   -- price selecting/specifying that kernel

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate f zero    x = x
iterate f (suc n) x = iterate f n (f x)

------------------------------------------------------------------------
-- A trace is “state after n steps”, observed by PDA.

TraceObs :
  ∀ {I S O : Set} →
  KernelFamily I S →
  PDA S O →
  I → Nat → S → O
TraceObs {I} {S} {O} F P i n s =
  PDA.observe P (iterate {S = S} (KernelFamily.K F i) n s)

------------------------------------------------------------------------
-- Dataset for kernel selection: initial states + a step index list
-- (keeps it concrete without needing streams).

record KSData (S : Set) : Set₁ where
  field
    inits : List S
    steps : List Nat

-- Flatten observations (cartesian product inits × steps)
concat : ∀ {A : Set} → List A → List A → List A
concat [] ys       = ys
concat (x ∷ xs) ys = x ∷ concat xs ys

map2 : ∀ {A B C : Set} → (A → B → C) → List A → List B → List C
map2 f []       _        = []
map2 f (a ∷ as) bs       = concat (map (f a) bs) (map2 f as bs)

ObsDatasetKS :
  ∀ {I S O : Set} →
  KernelFamily I S →
  PDA S O →
  I → KSData S → List O
ObsDatasetKS F P i D =
  map2 (λ s n → TraceObs F P i n s) (KSData.inits D) (KSData.steps D)

------------------------------------------------------------------------
-- A model over observations (two-part code)
record ObsModel (O : Set) : Set₁ where
  field
    Lmodel : CodeLength
    Ldata| : List O → CodeLength

MDLscore :
  ∀ {I S O : Set} →
  KernelFamily I S →
  PDA S O →
  ObsModel O →
  I → KSData S → CodeLength
MDLscore F P M i D =
  PDA.costPDA P
  + KernelFamily.Lkernel F i
  + ObsModel.Lmodel M
  + ObsModel.Ldata| M (ObsDatasetKS F P i D)

------------------------------------------------------------------------
-- Kernel-selection theorem statement: i* is MDL-minimal within the family.
-- (We keep “argmin” as an explicit proof obligation.)

record ArgMin {I S O : Set} (F : KernelFamily I S) (P : PDA S O) (M : ObsModel O)
              (D : KSData S) : Set₁ where
  field
    i* : I
    minimal :
      ∀ i →
        MDLscore F P M i* D ≤ MDLscore F P M i D
