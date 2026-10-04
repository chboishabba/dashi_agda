{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ComponentScalarRound829Exact where

------------------------------------------------------------------------
-- R829A / FINITE OUTPUT-SCALAR CERTIFICATE FOR THE 3-4-5 SNAPSHOT
--
-- The independent exact component evaluator expands the R828 witness into
-- eight nonzero fixed-output coherent-work rows and six initial-mode
-- production/dissipation rows.  This owner records the resulting rational
-- table and kernel-checks ONLY its finite aggregation.  The vector/helical
-- evaluation producing each row remains the concrete same-object leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNR650Rational345VectorWorkRound829Exact as Vector
import DASHI.Physics.Closure.NSTriadKNR650Rational345EnergyRowsRound829Exact as Energy

-- Fixed outputs, ordered lexicographically:
-- (-3,-4,0), (-3,0,0), (-3,4,0), (0,-4,0),
-- (0,4,0), (3,-4,0), (3,0,0), (3,4,0).
w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ : ℚ
w₁ = Vector.w₁
w₂ = Vector.w₂
w₃ = Vector.w₃
w₄ = Vector.w₄
w₅ = Vector.w₅
w₆ = Vector.w₆
w₇ = Vector.w₇
w₈ = Vector.w₈

totalWork : ℚ
totalWork =
  w₁ + w₂ + w₃ + w₄ + w₅ + w₆ + w₇ + w₈

totalWorkExact :
  totalWork ≡ - ((+ 557627) / 125)
totalWorkExact
  rewrite Vector.w₁Exact | Vector.w₂Exact | Vector.w₃Exact | Vector.w₄Exact
        | Vector.w₅Exact | Vector.w₆Exact | Vector.w₇Exact | Vector.w₈Exact =
  solve []

-- Initial nonzero velocity modes:
-- (-3,-4,0), (-3,0,0), (0,-4,0), (0,4,0), (3,0,0), (3,4,0).
p₁ p₂ p₃ p₄ p₅ p₆ : ℚ
p₁ = Energy.p₁
p₂ = Energy.p₂
p₃ = Energy.p₃
p₄ = Energy.p₄
p₅ = Energy.p₅
p₆ = Energy.p₆

totalProduction : ℚ
totalProduction = p₁ + p₂ + p₃ + p₄ + p₅ + p₆

totalProductionExact : totalProduction ≡ 0ℚ
totalProductionExact
  rewrite Energy.p₁Exact | Energy.p₂Exact | Energy.p₃Exact
        | Energy.p₄Exact | Energy.p₅Exact | Energy.p₆Exact =
  solve []

d₁ d₂ d₃ d₄ d₅ d₆ : ℚ
d₁ = Energy.d₁
d₂ = Energy.d₂
d₃ = Energy.d₃
d₄ = Energy.d₄
d₅ = Energy.d₅
d₆ = Energy.d₆

totalDissipation : ℚ
totalDissipation = d₁ + d₂ + d₃ + d₄ + d₅ + d₆

totalDissipationExact : totalDissipation ≡ 15834
totalDissipationExact
  rewrite Energy.d₁Exact | Energy.d₂Exact | Energy.d₃Exact
        | Energy.d₄Exact | Energy.d₅Exact | Energy.d₆Exact =
  solve []

round829AOutputWorkAggregationClosed : Bool
round829AOutputWorkAggregationClosed = true

round829AProductionAggregationClosed : Bool
round829AProductionAggregationClosed = true

round829ADissipationAggregationClosed : Bool
round829ADissipationAggregationClosed = true

round829AComponentVectorEvaluationSameObjectClosed : Bool
round829AComponentVectorEvaluationSameObjectClosed = false

round829AComponentVectorEvaluationSameObjectClosedIsFalse :
  round829AComponentVectorEvaluationSameObjectClosed ≡ false
round829AComponentVectorEvaluationSameObjectClosedIsFalse = refl
