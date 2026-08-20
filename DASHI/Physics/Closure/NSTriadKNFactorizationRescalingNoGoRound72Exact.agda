module DASHI.Physics.Closure.NSTriadKNFactorizationRescalingNoGoRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- ROUND72 / FACTORIZATION NON-CANONICITY FALSIFIER
--
-- Weighted Cauchy is useful only if its factors are physically determined.
-- The scalar identity a=x*y alone does NOT determine charge=sum x^2 or
-- effectiveComplexity=sum y^2: reciprocal rescaling changes both while leaving
-- a unchanged.
--
-- This file gives an exact singleton witness for a=1:
--
--   (x,y)=(1,1)       -> charge=1, complexity=1,
--   (x,y)=(2,1/2)     -> charge=4, complexity=1/4,
--
-- while both products are exactly 1.  Therefore no favorable weighted Cauchy
-- budget may be inferred from LocalizedPDEAtom.value alone.  The missing
-- physical overlay must be supplied by actual velocity/Gram/energy factors.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective

unitFactors : List Effective.FactorizedContribution
unitFactors = Effective.factorized-contribution 1ℚ 1ℚ ∷ []

rescaledFactors : List Effective.FactorizedContribution
rescaledFactors =
  Effective.factorized-contribution Scale.two Scale.half ∷ []

unitProductIsOne :
  Effective.factorizedSignedSum unitFactors ≡ 1ℚ
unitProductIsOne = solve []

rescaledProductIsOne :
  Effective.factorizedSignedSum rescaledFactors ≡ 1ℚ
rescaledProductIsOne = solve []

unitChargeIsOne :
  Effective.concentrationCharge unitFactors ≡ 1ℚ
unitChargeIsOne = solve []

unitComplexityIsOne :
  Effective.effectiveComplexity unitFactors ≡ 1ℚ
unitComplexityIsOne = solve []

rescaledChargeIsFour :
  Effective.concentrationCharge rescaledFactors
  ≡ Scale.two * Scale.two
rescaledChargeIsFour = solve []

rescaledComplexityIsQuarter :
  Effective.effectiveComplexity rescaledFactors
  ≡ Scale.half * Scale.half
rescaledComplexityIsQuarter = solve []

round72ScalarValueAloneDeterminesEffectiveComplexity : Bool
round72ScalarValueAloneDeterminesEffectiveComplexity = false

round72PhysicalFactorizationAuthorityRequired : Bool
round72PhysicalFactorizationAuthorityRequired = true

round72ScalarValueAloneDeterminesEffectiveComplexityIsFalse :
  round72ScalarValueAloneDeterminesEffectiveComplexity ≡ false
round72ScalarValueAloneDeterminesEffectiveComplexityIsFalse = refl

round72PhysicalFactorizationAuthorityRequiredIsTrue :
  round72PhysicalFactorizationAuthorityRequired ≡ true
round72PhysicalFactorizationAuthorityRequiredIsTrue = refl
