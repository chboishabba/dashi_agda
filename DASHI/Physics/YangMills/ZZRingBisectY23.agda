module DASHI.Physics.YangMills.ZZRingBisectY23 where

{-# OPTIONS -v bisect:10 #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Reflection.TCM.Syntax
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)

pivot : ℚ
pivot = + 481 / 1379

macro
  normPivot : Term → TC ⊤
  normPivot hole = do
    t ← normalise (def (quote pivot) [])
    debugPrint "bisect" 10 (strErr "normalise gave: " ∷ termErr t ∷ [])
    unify hole (con (quote tt) [])

check : ⊤
check = normPivot
