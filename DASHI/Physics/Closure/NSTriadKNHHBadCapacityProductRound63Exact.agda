module DASHI.Physics.Closure.NSTriadKNHHBadCapacityProductRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 / A2
--
-- The downstream hard viscosity tax never consumes the selected HH-bad
-- ceiling C_* and unmasked-charge multiplicity K_bad separately.  It consumes
-- only
--
--       Lambda_bad = C_* K_bad
--
-- through
--
--       eta_HHb = 2 Lambda_bad.
--
-- Make that optimization variable explicit.  This allows the physical A2
-- producer to trade a larger ceiling against a smaller charge multiplicity (or
-- conversely) without pretending either factor must be separately optimal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityKBadRound61Exact as Gate

badCapacityProduct : ℚ → ℚ → ℚ
badCapacityProduct ceiling multiplicity = ceiling * multiplicity

hhBadTaxFromCapacityProduct : ℚ → ℚ
hhBadTaxFromCapacityProduct lambdaBad = Sharp.two * lambdaBad

hhBadTaxFactorsOnlyThroughCapacityProduct :
  ∀ ceiling multiplicity →
  Gate.hhBadTax ceiling multiplicity
  ≡ hhBadTaxFromCapacityProduct (badCapacityProduct ceiling multiplicity)
hhBadTaxFactorsOnlyThroughCapacityProduct ceiling multiplicity =
  solve (ceiling ∷ multiplicity ∷ [])

sameCapacityProductSameHardTax :
  ∀ c₁ k₁ c₂ k₂ →
  badCapacityProduct c₁ k₁ ≡ badCapacityProduct c₂ k₂ →
  Gate.hhBadTax c₁ k₁ ≡ Gate.hhBadTax c₂ k₂
sameCapacityProductSameHardTax c₁ k₁ c₂ k₂ same =
  let
    left = hhBadTaxFactorsOnlyThroughCapacityProduct c₁ k₁
    right = hhBadTaxFactorsOnlyThroughCapacityProduct c₂ k₂
  in
  trans left (trans (cong hhBadTaxFromCapacityProduct same) (sym right))

round63A2OptimizesCapacityProductNotFactorsSeparately : Bool
round63A2OptimizesCapacityProductNotFactorsSeparately = true

round63A2OptimizesCapacityProductNotFactorsSeparatelyIsTrue :
  round63A2OptimizesCapacityProductNotFactorsSeparately ≡ true
round63A2OptimizesCapacityProductNotFactorsSeparatelyIsTrue = refl
