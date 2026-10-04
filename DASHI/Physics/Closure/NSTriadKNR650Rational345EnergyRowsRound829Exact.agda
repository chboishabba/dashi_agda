{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345EnergyRowsRound829Exact where

------------------------------------------------------------------------
-- R829C / EXACT PRODUCTION AND DISSIPATION ROWS FROM 3-4-5 VECTORS
--
-- This owner evaluates the six nonzero initial velocity modes against the
-- exact projected-nonlinearity vectors emitted by the R829 component
-- certificate.  The scalar consumers are the same real Hermitian pairing and
-- C^3 norm used throughout the rational periodic stack.
--
-- Remaining physical leaf: prove that these forcing vectors are literally
-- Audit.projectedNonlinearity of the concrete radius-four snapshot.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _/_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179

F : C3.RealField _
F = Rational.rationalRealField

c : ℚ → ℚ → C3.Complex F
c = C3.complex

v : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → C3.Complex3 F
v xr xi yr yi zr zi =
  C3.complex3 (c xr xi) (c yr yi) (c zr zi)

two : ℚ
two = 2

productionRow :
  ℚ → C3.Complex3 F → C3.Complex3 F → ℚ
productionRow weight velocity forcing =
  two * weight * R179.realHermitianCross velocity forcing

dissipationRow :
  ℚ → ℚ → C3.Complex3 F → ℚ
dissipationRow weight normSquared velocity =
  weight * normSquared * L2.complex3NormSquared velocity

-- (-3,-4,0)
u₁ f₁ : C3.Complex3 F
u₁ = v 0 (- 6) 0 ((+ 9) / 2) (- 2) (- 2)
f₁ = v ((+ 224) / 25) 0 (- ((+ 168) / 25)) 0 14 (- 6)

-- (-3,0,0)
u₂ f₂ : C3.Complex3 F
u₂ = v 0 0 2 (- 2) (- 2) 1
f₂ = v 0 0 (- 27) (- 27) 60 36

-- (0,-4,0)
u₃ f₃ : C3.Complex3 F
u₃ = v 2 (- 2) 0 0 2 (- 2)
f₃ = v 48 48 0 0 68 18

-- (0,4,0)
u₄ f₄ : C3.Complex3 F
u₄ = v 2 2 0 0 2 2
f₄ = v 48 (- 48) 0 0 68 (- 18)

-- (3,0,0)
u₅ f₅ : C3.Complex3 F
u₅ = v 0 0 2 2 (- 2) (- 1)
f₅ = v 0 0 (- 27) 27 60 (- 36)

-- (3,4,0)
u₆ f₆ : C3.Complex3 F
u₆ = v 0 6 0 (- ((+ 9) / 2)) (- 2) 2
f₆ = v ((+ 224) / 25) 0 (- ((+ 168) / 25)) 0 14 6

p₁ p₂ p₃ p₄ p₅ p₆ : ℚ
p₁ = productionRow 4 u₁ f₁
p₂ = productionRow 4 u₂ f₂
p₃ = productionRow 4 u₃ f₃
p₄ = productionRow 4 u₄ f₄
p₅ = productionRow 4 u₅ f₅
p₆ = productionRow 4 u₆ f₆

p₁Exact : p₁ ≡ - 128
p₁Exact = solve []
p₂Exact : p₂ ≡ - 672
p₂Exact = solve []
p₃Exact : p₃ ≡ 800
p₃Exact = solve []
p₄Exact : p₄ ≡ 800
p₄Exact = solve []
p₅Exact : p₅ ≡ - 672
p₅Exact = solve []
p₆Exact : p₆ ≡ - 128
p₆Exact = solve []

d₁ d₂ d₃ d₄ d₅ d₆ : ℚ
d₁ = dissipationRow 4 25 u₁
d₂ = dissipationRow 4 9 u₂
d₃ = dissipationRow 4 16 u₃
d₄ = dissipationRow 4 16 u₄
d₅ = dissipationRow 4 9 u₅
d₆ = dissipationRow 4 25 u₆

d₁Exact : d₁ ≡ 6425
d₁Exact = solve []
d₂Exact : d₂ ≡ 468
d₂Exact = solve []
d₃Exact : d₃ ≡ 1024
d₃Exact = solve []
d₄Exact : d₄ ≡ 1024
d₄Exact = solve []
d₅Exact : d₅ ≡ 468
d₅Exact = solve []
d₆Exact : d₆ ≡ 6425
d₆Exact = solve []

round829CProductionRowsFromExactVectorsClosed : Bool
round829CProductionRowsFromExactVectorsClosed = true

round829CDissipationRowsFromExactVectorsClosed : Bool
round829CDissipationRowsFromExactVectorsClosed = true

round829CProjectedNonlinearityVectorsSameObjectClosed : Bool
round829CProjectedNonlinearityVectorsSameObjectClosed = false

round829CCriticalFoldSameObjectClosed : Bool
round829CCriticalFoldSameObjectClosed = false

round829CClayPromotion : Bool
round829CClayPromotion = false
