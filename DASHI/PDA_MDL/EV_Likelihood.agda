module DASHI.PDA_MDL.EV_Likelihood where

open import DASHI.PDA_MDL.Prelude
open import DASHI.PDA_MDL.ExponentVector
open import Data.Vec using (Vec; []; _∷_; zipWith; foldr′; map)

------------------------------------------------------------------------
-- Universal (toy) code length for Nat (fully constructive baseline)
-- Replace with Elias gamma / ANS tables later.

lenNat : Nat → CodeLength
lenNat n = suc n  -- unary length: 1 + n (baseline, simple)

lenEV : EV → CodeLength
lenEV = foldr′ (λ e acc → lenNat e + acc) zero

lenDataset : DatasetEV → CodeLength
lenDataset []       = zero
lenDataset (x ∷ xs) = lenEV x + lenDataset xs

------------------------------------------------------------------------
-- Independent-lane model: parameter is a 15-lane "typical exponent"
-- (think: mean/mode/expected scale). You can generalize later.

record IndepEVModel : Set where
  field
    θ : EV

-- Model description length (price the parameters)
Lmodel : IndepEVModel → CodeLength
Lmodel M = lenEV (IndepEVModel.θ M)

-- Data given model: price residuals per lane (|e - θ|) with unary code
abs : Nat → Nat → Nat
abs zero    n       = n
abs (suc m) zero    = suc m
abs (suc m) (suc n) = abs m n

residualEV : EV → EV → EV
residualEV x θ = zipWith abs x θ

Ldata| : IndepEVModel → DatasetEV → CodeLength
Ldata| M []       = zero
Ldata| M (x ∷ xs) = lenEV (residualEV x (IndepEVModel.θ M)) + Ldata| M xs

-- Total two-part MDL
MDL : IndepEVModel → DatasetEV → CodeLength
MDL M D = Lmodel M + Ldata| M D

------------------------------------------------------------------------
-- A concrete "fit" choice from data: θ := max lane observed (cheap) or mean.
-- Here: θ := stats D  (sum) is too big; instead use per-lane capped statistic.
-- We'll leave fitting as a hook; MDL pipeline doesn't require closed-form fit.

postulate
  fit : DatasetEV → IndepEVModel
