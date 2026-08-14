{-# OPTIONS -v bisect:10 #-}

module DASHI.Physics.YangMills.ZZRingBisectY25 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Reflection.TCM.Syntax
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)

pivot : ℚ
pivot = + 13919 / 5516

macro
  normPivot : Term → TC ⊤
  normPivot hole = do
    t ← normalise (def (quote pivot) [])
    debugPrint "bisect" 10 (strErr "normalise gave: " ∷ termErr t ∷ [])
    unify hole (con (quote tt) [])

check : ⊤
check = normPivot
