module DASHI.Physics.YangMills.ZZRingBisectY22 where

{-# OPTIONS -v bisect:10 #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Reflection.TCM.Syntax
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)

pivot2 : ℚ
pivot2 = + 13919 / 5516

macro
  normPivot2 : Term → TC ⊤
  normPivot2 hole = do
    t ← normalise (def (quote pivot2) [])
    debugPrint "bisect" 10 (strErr "normalise pivot2 gave: " ∷ termErr t ∷ [])
    unify hole (con (quote tt) [])

check : ⊤
check = normPivot2
