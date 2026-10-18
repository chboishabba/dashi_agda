{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345VectorWorkRound829Exact where

------------------------------------------------------------------------
-- R829B / EXACT VECTOR -> COHERENT-WORK EVALUATION FOR THE 3-4-5 SNAPSHOT
--
-- The independent component certificate emits eight nonzero fixed-output
-- mixed vectors M_k and commutator vectors G_k.  This owner embeds those exact
-- rational complex vectors into the SAME R692 coherentWork consumer and
-- kernel-checks every scalar row.
--
-- Remaining R829 leaf after this file:
--   prove Work.fixedOutputMixedProduct = M_k and
--         Work.fixedOutputCommutator = G_k
-- on the concrete radius-four repository snapshot.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work

F : C3.RealField _
F = Rational.rationalRealField

c : ℚ → ℚ → C3.Complex F
c = C3.complex

v : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → C3.Complex3 F
v xr xi yr yi zr zi =
  C3.complex3 (c xr xi) (c yr yi) (c zr zi)

-- k = (-3,-4,0)
m₁ g₁ : C3.Complex3 F
m₁ = v (- 7) (- 1) (- 7) (- 1) (- 1) 1
g₁ = v 8 (- 23) 8 (- 23) (- 98) (- 56)

-- k = (-3,0,0)
m₂ g₂ : C3.Complex3 F
m₂ =
  v (- ((+ 21) / 10)) (- ((+ 9) / 2))
    ((+ 7) / 10) ((+ 3) / 2)
    (- ((+ 69) / 10)) (- ((+ 9) / 2))
g₂ =
  v (- ((+ 246) / 5)) 42
    ((+ 858) / 25) (- ((+ 678) / 25))
    (- ((+ 909) / 5)) ((+ 225) / 2)

-- k = (-3,4,0)
m₃ g₃ : C3.Complex3 F
m₃ = v 1 1 (- 1) (- 1) (- 1) 7
g₃ = v 2 (- 35) (- 2) 35 308 50

-- k = (0,-4,0)
m₄ g₄ : C3.Complex3 F
m₄ =
  v (- ((+ 9) / 5)) (- ((+ 17) / 5))
    ((+ 18) / 5) ((+ 34) / 5)
    (- ((+ 46) / 5)) (- 3)
g₄ =
  v ((+ 2913) / 50) (- ((+ 833) / 50))
    (- ((+ 117) / 5)) (- ((+ 171) / 5))
    ((+ 5428) / 25) (- ((+ 5412) / 25))

-- k = (0,4,0): conjugate row
m₅ g₅ : C3.Complex3 F
m₅ =
  v (- ((+ 9) / 5)) ((+ 17) / 5)
    ((+ 18) / 5) (- ((+ 34) / 5))
    (- ((+ 46) / 5)) 3
g₅ =
  v ((+ 2913) / 50) ((+ 833) / 50)
    (- ((+ 117) / 5)) ((+ 171) / 5)
    ((+ 5428) / 25) ((+ 5412) / 25)

-- k = (3,-4,0)
m₆ g₆ : C3.Complex3 F
m₆ = v 1 (- 1) (- 1) 1 (- 1) (- 7)
g₆ = v 2 35 (- 2) (- 35) 308 (- 50)

-- k = (3,0,0)
m₇ g₇ : C3.Complex3 F
m₇ =
  v (- ((+ 21) / 10)) ((+ 9) / 2)
    ((+ 7) / 10) (- ((+ 3) / 2))
    (- ((+ 69) / 10)) ((+ 9) / 2)
g₇ =
  v (- ((+ 246) / 5)) (- 42)
    ((+ 858) / 25) ((+ 678) / 25)
    (- ((+ 909) / 5)) (- ((+ 225) / 2))

-- k = (3,4,0)
m₈ g₈ : C3.Complex3 F
m₈ = v (- 7) 1 (- 7) 1 (- 1) (- 1)
g₈ = v 8 23 8 23 (- 98) 56

w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ : ℚ
w₁ = Work.coherentWork m₁ g₁
w₂ = Work.coherentWork m₂ g₂
w₃ = Work.coherentWork m₃ g₃
w₄ = Work.coherentWork m₄ g₄
w₅ = Work.coherentWork m₅ g₅
w₆ = Work.coherentWork m₆ g₆
w₇ = Work.coherentWork m₇ g₇
w₈ = Work.coherentWork m₈ g₈

w₁Exact : w₁ ≡ - 48
w₁Exact = solve []

w₂Exact : w₂ ≡ (+ 322917) / 250
w₂Exact = solve []

w₃Exact : w₃ ≡ - 48
w₃Exact = solve []

w₄Exact : w₄ ≡ - ((+ 428272) / 125)
w₄Exact = solve []

w₅Exact : w₅ ≡ - ((+ 428272) / 125)
w₅Exact = solve []

w₆Exact : w₆ ≡ - 48
w₆Exact = solve []

w₇Exact : w₇ ≡ (+ 322917) / 250
w₇Exact = solve []

w₈Exact : w₈ ≡ - 48
w₈Exact = solve []

round829BAllEightVectorWorkRowsClosed : Bool
round829BAllEightVectorWorkRowsClosed = true

round829BUsesLiteralR692CoherentWorkConsumer : Bool
round829BUsesLiteralR692CoherentWorkConsumer = true

round829BR224MixedVectorsSameObjectClosed : Bool
round829BR224MixedVectorsSameObjectClosed = false

round829BR230CommutatorVectorsSameObjectClosed : Bool
round829BR230CommutatorVectorsSameObjectClosed = false

round829BClayPromotion : Bool
round829BClayPromotion = false

round829BAllEightVectorWorkRowsClosedIsTrue :
  round829BAllEightVectorWorkRowsClosed ≡ true
round829BAllEightVectorWorkRowsClosedIsTrue = refl
