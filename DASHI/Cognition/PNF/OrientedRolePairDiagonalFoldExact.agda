{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.OrientedRolePairDiagonalFoldExact where

------------------------------------------------------------------------
-- Concrete fold for oriented source/target role states.
--
-- For a fine pair (source,target), phase inversion swaps the role blocks.
-- The fixed locus is therefore the diagonal source = target, not a distinguished
-- numerical zero.  This is the exact high-dimensional version of the scalar
-- ternary fold used by requested role-orientation observations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Cognition.PNF.RequestedFibreInvolutionFoldExact as Fold

record RolePairState (A : Set) : Set where
  constructor rolePairState
  field
    source target : A

open RolePairState public

swapRoles : ∀ {A : Set} → RolePairState A → RolePairState A
swapRoles (rolePairState source target) = rolePairState target source

swapRolesInvolutive :
  ∀ {A : Set} (state : RolePairState A) →
  swapRoles (swapRoles state) ≡ state
swapRolesInvolutive (rolePairState source target) = refl

roleSwapInvolution :
  ∀ {A : Set} → Fold.FineInvolution (RolePairState A)
roleSwapInvolution = Fold.fineInvolution swapRoles swapRolesInvolutive

swapFixedImpliesDiagonal :
  ∀ {A : Set} (state : RolePairState A) →
  swapRoles state ≡ state →
  source state ≡ target state
swapFixedImpliesDiagonal state fixed = cong source fixed

diagonalImpliesSwapFixed :
  ∀ {A : Set} (state : RolePairState A) →
  source state ≡ target state →
  swapRoles state ≡ state
diagonalImpliesSwapFixed (rolePairState source .source) refl = refl

record RolePairDiagonalFoldWitness {A : Set} (state : RolePairState A) : Set where
  constructor rolePairDiagonalFoldWitness
  field
    sourceEqualsTarget : source state ≡ target state
    fixedByRoleSwap : swapRoles state ≡ state

open RolePairDiagonalFoldWitness public

compileDiagonalFold :
  ∀ {A : Set} (state : RolePairState A) →
  source state ≡ target state →
  RolePairDiagonalFoldWitness state
compileDiagonalFold state diagonal =
  rolePairDiagonalFoldWitness diagonal (diagonalImpliesSwapFixed state diagonal)
