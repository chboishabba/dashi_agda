{-# OPTIONS -v bisect:10 #-}

module DASHI.Physics.YangMills.ZZRingBisectQ2 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Reflection.TCM.Syntax
open import Reflection.AST using (vArg)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.GCD using (gcd)

macro
  normGCD : Term → TC ⊤
  normGCD hole = do
    t ← normalise (def (quote gcd) (vArg (lit (nat 13919)) ∷ vArg (lit (nat 5516)) ∷ []))
    debugPrint "bisect" 10 (strErr "normalise gave: " ∷ termErr t ∷ [])
    unify hole (con (quote tt) [])

check : ⊤
check = normGCD
