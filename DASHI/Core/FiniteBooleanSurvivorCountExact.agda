module DASHI.Core.FiniteBooleanSurvivorCountExact where

------------------------------------------------------------------------
-- FINITE BOOLEAN SURVIVOR COUNT
--
-- Encode a finite family of branch continuations by Bool:
--
--   true  = survives the block,
--   false = hits the stopping set during the block.
--
-- If at least one continuation is killed, the survivor count is strictly less
-- than the total number of continuations, hence at most length-1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)
open import Data.List.Base using (length)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using
  (≤-trans; ≤-<-trans; n<1+n; n≤1+n)

survivorCount : List Bool → Nat
survivorCount [] = zero
survivorCount (false ∷ xs) = survivorCount xs
survivorCount (true ∷ xs) = suc (survivorCount xs)

survivorCountLeLength :
  (xs : List Bool) → survivorCount xs ≤ length xs
survivorCountLeLength [] = z≤n
survivorCountLeLength (false ∷ xs) =
  ≤-trans
    (survivorCountLeLength xs)
    (n≤1+n (length xs))
survivorCountLeLength (true ∷ xs) =
  s≤s (survivorCountLeLength xs)

countBelowSuccessorLength :
  (xs : List Bool) → survivorCount xs < suc (length xs)
countBelowSuccessorLength xs =
  ≤-<-trans (survivorCountLeLength xs) (n<1+n (length xs))

falseMemberForcesStrictLoss :
  {xs : List Bool} →
  false ∈ xs →
  survivorCount xs < length xs
falseMemberForcesStrictLoss {false ∷ xs} membership =
  countBelowSuccessorLength xs
falseMemberForcesStrictLoss {true ∷ xs} (there membership) =
  s≤s (falseMemberForcesStrictLoss membership)

strictBelowImpliesLePred :
  {m n : Nat} → m < n → m ≤ n - 1
strictBelowImpliesLePred {m} {zero} ()
strictBelowImpliesLePred {m} {suc n} (s≤s m≤n) = m≤n

falseMemberForcesAtMostLengthMinusOne :
  {xs : List Bool} →
  false ∈ xs →
  survivorCount xs ≤ length xs - 1
falseMemberForcesAtMostLengthMinusOne membership =
  strictBelowImpliesLePred (falseMemberForcesStrictLoss membership)
